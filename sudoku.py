# module pyclips sous windows avec python 2.5.4
import clips
class grille:   
    def __init__(self,values='2*5***8***186934*239***5****7*26*****46***28*****51*9****3***286*378954***1***6*3',alphabet='123456789',blocsize=(3,3),debug=False):
        self.size = len(alphabet)
        self.alphabet = [alphabet[i] for i in xrange(self.size)]
        self.blocsize = blocsize
        self.resultat = ''
        self.env = clips.Environment()
        self.env.Clear()          
        self.memo = []
# les règles du sudoku
        self.env.BuildRule('reducCase','(valeur ?v connu ?x ?y ?z) ?c <- (valeur ? possible ?x ?y ?z)','(retract ?c)')
        self.env.BuildRule('reducBloc','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y2 ?z1)','(retract ?c)')
        self.env.BuildRule('reducColonne','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y1 ?z2)','(retract ?c)')
        self.env.BuildRule('reducLigne','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x1 ?y2 ?z2)','(retract ?c)') 
# alphabet
        self.env.BuildDeffacts('alphabet',''.join(['(lettre '+str(i)+')' for i in self.alphabet]))    
# dimension d'un bloc
        self.env.BuildDeffacts('bloc','(bloc '+str(blocsize[0])+' '+str(blocsize[1])+'))')

        if debug:
            print('(defrule reducCase (valeur ?v connu ?x ?y ?z) ?c <- (valeur ? possible ?x ?y ?z) => (retract ?c))')
            print('(defrule reducBloc (valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y2 ?z1) => (retract ?c))')
            print('(defrule reducColonne (valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y1 ?z2) => (retract ?c))')
            print('(defrule reducLigne (valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x1 ?y2 ?z2) => (retract ?c))') 
            print('(deffacts alphabet '+''.join(['(lettre '+str(i)+')' for i in self.alphabet])+')')    
            print('(deffacts bloc (bloc '+str(blocsize[0])+' '+str(blocsize[1])+'))')

#initialisation des compteur
        self.rowcount = [0] * self.size
        self.colcount = [0] * self.size
        self.blkcount = [0] * self.size
#initialisation de la grille
        self.tab = []
        for l in xrange(self.size):
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
                if tmp in alphabet :
                    self.tab[i][j] = int(tmp)                        
# recensement par ligne, colonne et par bloc
                    self.rowcount[i] += 1
                    self.colcount[j] += 1
                    self.blkcount[blk] += 1
## insertion des valeurs connues
                    facts.append('(valeur '+str(tmp)+' connu '+str(ligne)+' '+str(colonne)+' '+str(bloc)+')')
                else:
                    self.resultat += '(assert(valeur ?a'+str(ligne)+'_'+str(colonne)+' resultat '+str(ligne)+' '+str(colonne)+' '+str(bloc)+'))'
# insertion des cas possibles
                self.env.BuildDeffacts('case' + '-'.join([str(ligne),str(colonne)]),''.join(['(valeur '+str(k)+' possible '+str(ligne)+' '+str(colonne)+' '+str(bloc)+')' for k in self.alphabet]))                    
                if debug:
                    print('(deffacts case'+ '-'.join([str(ligne),str(colonne)])+' '+''.join(['(valeur '+str(k)+' possible '+str(ligne)+' '+str(colonne)+' '+str(bloc)+')' for k in self.alphabet])+')')

        self.env.BuildDeffacts('connus',''.join([l for l in facts]))
        self.env.Reset()      
        if debug:
            print('(deffacts connus '+''.join([l for l in facts])+')')
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
            else:
                if c[1]==j:
                    result.append(c)
                else:
                    if c[0]==i:
                        result.append(c)
        return result      
    def constructRule(self,i,j,k):       
        rule = ''            
        ligne,colonne,bloc = i+1,j+1,k+1
        if str(self.tab[i][j]) not in self.alphabet:
          rule += '(valeur ?a' + str(ligne) + '_' + str(colonne)
          for m in self.getPrec(i,j,k):
              rule += '&~?a' + str(m[0]+1) + '_' + str(m[1]+1)                       
          rule += ' possible '+ str(ligne) + ' '+ str(colonne) +' '+ str(bloc) +') '
          self.memo.append((i,j,k))
        return rule
    def resolve(self,debug=False):
        self.soluce=''
        d = {max(self.blkcount):('bloc',self.blkcount),max(self.colcount):('colonne',self.colcount),max(self.rowcount):('ligne',self.rowcount)}
        (t,a) = d[max(d.keys())]
        if t == 'ligne':
            self.soluce = ''.join([self.constructRule(i,j,self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(len(self.alphabet))])
            if debug:
                print('(defrule solutionLigne '+ self.soluce +' => '+ self.resultat + ' ) ')
            self.env.BuildRule('solutionLigne',self.soluce,self.resultat)
        if t == 'colonne':
            self.soluce = ''.join([self.constructRule(j,i,self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(len(self.alphabet))])
            if debug:
                print('(defrule solutionColonne '+self.soluce+' => '+self.resultat+' ) ')
            self.env.BuildRule('solutionColonne',self.soluce,self.resultat)
        if t == 'bloc':
            self.soluce = ''.join([self.constructRule((j+i)/self.blocsize[0],(k+i)%self.blocsize[1],self.getBloc(i,j)[1]) for i in self.creerIndex(a) for j in range(self.blocsize[0]) for k in range(self.blocsize[1])])
            if debug:
                print('(defrule solutionBloc '+ self.soluce +' => '+ self.resultat +' ) ')
            self.env.BuildRule('solutionBloc',self.soluce,self.resultat)
        self.env.Run()
#        for i in self.resultat:
#            self.env.facts.append(i)
