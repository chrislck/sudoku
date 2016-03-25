import clips
class grille:        
    def __init__(self,values='',alphabet=(1,2,3,4,5,6,7,8,9),blocsize=(3,3)):
        self.env = clips.Environment()
        self.env.clear()          
        self.env.BuildRule('reducBloc','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y2 ?z1)','(retract ?c)')
        self.env.BuildRule('reducColonne','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x2 ?y1 ?z2)','(retract ?c)')
        self.env.BuildRule('reducLigne','(valeur ?v1 connu ?x1 ?y1 ?z1) ?c <- (valeur ?v1 possible ?x1 ?y2 ?z2)','(retract ?c)') 
        self.size = len(alphabet)
        self.alphabet = alphabet            
        for i in alphabet:
            env.Assert('(alphabet '+i+')')           
        self.blocsize = blocsize
        self.env.Assert ('(bloc '+blocsize[0]+' '+blocsize[1]+')')
        self.rowcount = [0] * self.size
        self.colcount = [0] * self.size
        self.blkcount = [0] * self.size        
        self.tab = [[None] * self.size] * self.size
        self.memoprec = []            
        self.resultat = ''
        self.resRuleLHS = ''
        self.resRuleRHS = ''
        if len(values) == self.size * self.size:
            for i in xrange(self.size):
                self.resRuleRHS += '(printout t '
                for j in xrange(self.size):
                    offset,bloc = self.getBloc(i,j)
                    tmp = values[offset] 
                    ligne,colonne,bloc = i+1,j+1,bloc+1
                    self.resultat += '(assert (valeur ?a'+ligne+'_'+colonne+' resultat '+ligne+' '+colonne+' '+bloc+'))'
                    self.resRuleLHS += '(valeur ?a'+ligne+'_'+colonne+' resultat '+ligne+' '+colonne+' '+bloc+')'            
                    self.resRuleRHS += '?a'+ligne+'_'+colonne + ' '
                    if tmp in alphabet:
                        tab[i][j] = tmp
# recensement par ligne, colonne et par bloc
                        self.rowcount[i] += 1
                        self.colcount[j] += 1
                        self.blkcount[bloc] += 1
# insertion des valeurs connues
                        self.env.Assert('(valeur '+tmp+' connu '+ligne+' '+colonne+' '+bloc+')')
                    else:
                        tab[i][j] = None
# insertion des cas possibles
                        for k in alphabet:
                            self.env.Assert('(valeur '+tmp+' possible '+ligne+' '+colonne+' '+bloc+')')
                self.RuleRHS += ') '
        self.env.BuildRule('afficheResultat',self.resRuleLHS,self.resRuleRHS)
# nettoyage avec les regles reduc-
        self.env.reset()
        self.env.run()
    def getBloc(self,i,j):
        offset = i * self.size + j
        return offset,((offset) / self.blocsize[0]) + ((offset) % self.blocsize[1])  
    def resolve(self):
        def creerIndex(a):
            b = a.copy()
            order =[]
            for j in range(len(a)):
                order.append(b.pop(b.index(max(b))))
            return order
        def constructRule(i,j):       
            def getPrec(i,j,memo):
                result = []
                bloc = self.getBloc(i,j)[1]
                for k in memo:
                    if self.getBloc(k[0],k[1])[1] == bloc:
                        result.append(k)
                    if k[1]==j:
                            result.append(k)
                    if k[0]==i:
                            result.append(k)
                return result      
            rule = ''            
            bloc = self.getBloc(i,j)[1]
            ligne,colonne,bloc = i+1,j+1,bloc+1
            if tab[i][j] in self.alphabet:
                rule += '(valeur ?a' + ligne + '_' + colonne +' connu '+ ligne + ' '+ colonne +' '+ bloc +') '
            else:
                rule += '(valeur ?a' + ligne + '_' + colonne
                for k in getPrec(i,j,self.memoprec):
                    rule += '&~?a' + k[0] + '_' + k[1]                       
                rule += ' connu|possible&~resultat '+ ligne + ' '+ colonne +' '+ bloc +') '
                self.memoprec.append((ligne,colonne,bloc))
            return rule
        d = {max(self.bloccount):('bloc',self.bloccount),max(self.colcount):('colonne',self.colcount),max(self.rowcount):('ligne',self.rowcount)}
        (t,a) = d[max(d.keys())]
        if t == 'ligne':
            self.env.BuildRule('solutionLigne',''.join([constructRule(i,j) for i in a for j in range(len(self.alphabet))]),self.resultat)
        if t == 'colonne':
            self.env.BuildRule('solutionLigne',''.join([constructRule(j,i) for i in a for j in range(len(self.alphabet))]),self.resultat)
        if t == 'bloc':
            self.env.BuildRule('solutionLigne',''.join([constructRule((j+i)/self.blocsize[0],(k+i)%self.blocsize[1]) for i in a for j in range(self.blocsize[0]) for k in range(self.blocsize[1])],self.resultat))
        self.env.run()
        
