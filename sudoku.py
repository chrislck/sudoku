# module pyclips sous windows avec python 2.5.4
import clips
class grille:        
    def __init__(self,values='8        123456789         598764321                  912345678                  ',alphabet=(1,2,3,4,5,6,7,8,9),blocsize=(3,3),debug=False):
        self.size = len(alphabet)
        self.alphabet = alphabet
        self.blocsize = blocsize
        self.resultat = ''
        self.env = clips.Environment()
        self.env.Clear()          
        self.memo = []
# les règles du sudoku
        self.env.BuildRule('reducCase','(valeur ?v connu|resulat ?x ?y ?z) ?c <- (valeur ? possible ?x ?y ?z)','(retract ?c)')
        self.env.BuildRule('reducBloc','(valeur ?v1 connu|resultat ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y2 ?z1)','(retract ?c)')
        self.env.BuildRule('reducColonne','(valeur ?v1 connu|resultat ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y1 ?z2)','(retract ?c)')
        self.env.BuildRule('reducLigne','(valeur ?v1 connu|resultat ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x1 ?y2 ?z2)','(retract ?c)') 
# alphabet
        self.env.BuildDeffacts('alphabet',''.join(['(alphabet '+str(i)+')' for i in self.alphabet]))    
# dimension d'un bloc
        self.env.BuildDeffacts('bloc','(bloc '+str(blocsize[0])+' '+str(blocsize[1])+'))')
#initialisation des compteur
        self.rowcount = [0] * self.size
        self.colcount = [0] * self.size
        self.blkcount = [0] * self.size
#initialisation de la grille
        self.tab = []
        for l in range(self.size):
            self.tab.append([None] * self.size)
#I/O padding 
        control = len(values) - self.blocsize[0]* self.blocsize[1] * self.size 
        if  control < 0:
            values = values + ' '*(abs(control))
        self.resultat = ''
#construction des faits connus (et aussi de la règle de résultats)
        facts = []
        for i in xrange(self.size):
            for j in xrange(self.size):
                offset,blk = self.getBloc(i,j)
                tmp = values[offset]
                ligne,colonne,bloc = i+1,j+1,blk+1
                self.resultat += '(assert (valeur ?a'+str(ligne)+'_'+str(colonne)+' resultat '+str(ligne)+' '+str(colonne)+' '+str(bloc)+'))'
# insertion des cas possibles
                self.env.BuildDeffacts('case' + '-'.join([str(ligne),str(colonne)]),''.join(['(valeur '+str(k)+' possible '+str(ligne)+' '+str(colonne)+' '+str(bloc)+')' for k in self.alphabet]))                    
                try:
                    if 0<int(tmp)<10 :
                        self.tab[i][j] = int(tmp)                        
                        self.memo.append((ligne,colonne,bloc))
# recensement par ligne, colonne et par bloc
                        self.rowcount[i] += 1
                        self.colcount[j] += 1
                        self.blkcount[blk] += 1
## insertion des valeurs connues
                        facts.append('(valeur '+str(tmp)+' connu '+str(ligne)+' '+str(colonne)+' '+str(bloc)+')')
                except ValueError:
                    pass
        self.env.Reset()
        for l in facts:
            self.env.Assert(l)
            self.env.Run()
# nettoyage avec les regles reduc-
    def getBloc(self,i,j):
        offset = i * self.size + j 
        return offset,i // self.blocsize[0]*self.blocsize[0] + j // self.blocsize[1] 
    def creerIndex(self,a):
        b = [a[i] for i in range(len(a))]
        order =[]
        for i in range(len(a)):
            t = b.index(max(b))
            order.append(t)
            b[t]=-1
        return order
    def getPrec(self,i,j,k):
        result = []
        for c in self.memo:
            if c[2] == k:
                result.append(c)
            if c[1]==j:
                result.append(c)
            if c[0]==i:
                result.append(c)
        return result      
    def constructRule(self,i,j,k):       
        rule = ''            
        ligne,colonne,bloc = i+1,j+1,k+1
        if self.tab[i][j] in self.alphabet:
            rule += '(valeur ?a' + str(ligne) + '_' + str(colonne) +' connu '+ str(ligne) + ' '+ str(colonne) +' '+ str(bloc) +') '
        else:
            rule += '(valeur ?a' + str(ligne) + '_' + str(colonne)
            for m in self.getPrec(i,j,k):
                rule += '&~?a' + str(m[0]) + '_' + str(m[1])                       
            rule += ' possible '+ str(ligne) + ' '+ str(colonne) +' '+ str(bloc) +') '
            self.memo.append((ligne,colonne,bloc))
        return rule
    def resolve(self,debug=False):
        soluce = ''
        d = {max(self.blkcount):('bloc',self.blkcount),max(self.colcount):('colonne',self.colcount),max(self.rowcount):('ligne',self.rowcount)}
        (t,a) = d[max(d.keys())]
        if t == 'ligne':
            soluce = ''.join([self.constructRule(i,j,self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(len(self.alphabet))])
            if debug:
                print('(defrule solutionLigne '+ soluce +'=>'+ self.resultat + ')')
            self.env.BuildRule('solutionLigne',soluce,self.resultat)
        if t == 'colonne':
            soluce = ''.join([self.constructRule(j,i,self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(len(self.alphabet))])
            if debug:
                print('(defrule solutionColonne '+soluce+'=>'+self.resultat+')')
            self.env.BuildRule('solutionColonne',soluce,self.resultat)
        if t == 'bloc':
            soluce = ''.join([self.constructRule((j+i)/self.blocsize[0],(k+i)%self.blocsize[1],self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(self.blocsize[0]) for k in range(self.blocsize[1])])
            if debug:
                print('(defrule solutionBloc '+ soluce +'=>'+ self.resultat +')')
            self.env.BuildRule('solutionBloc',soluce,self.resultat)
        if not debug:
            self.env.Run()
        
