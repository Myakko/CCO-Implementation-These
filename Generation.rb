#!/usr/bin/env ruby
#fait la normalisation de Baader de l'ontologie, pour que celle-ci ne possède plus que des axiomes de la forme :
# A subs B / A & B subs C / *rA subs B / A subs *rB
class GenerationOnto
   def initialize()
          @conceptTab=[]
      @roleTab=[]
      @conceptList=Hash.new("void")
      
    end


    def getConceptTab()
      return @conceptList
    end

    def getRoleTab()
      return @roleTab
    end

  def roleDepth(depth, roleTab, contenu)
   


    if depth>0
      pas = rand(depth)+1
      content = roleDepth(depth-pas, roleTab, contenu)
    else
      content = [contenu]
    end

      role=roleTab[rand(3)]
      roleChaine= "*"+role.to_s+"."
      chain1=[roleChaine, content]
    return chain1
  end

  def generateOnto(size, exp, compo, depth, maxLink, letter)
    ratio=100-exp
    ontology=[]
    roleTab=['r', 's', 't']
    @roleTab=['r', 's', 't']
    conceptTab=[]
    compoTab=[]
    compoConcept=[]
    @letter=letter
    @conceptList[@letter] =[]
    @depth=depth
    @exp=exp
    @maxLink=maxLink
    
    @number=maxLink+1
    starting=maxLink
    chain2=""+letter+"-0"
    for i in 1..starting do
      axiom=[]
      chain1=""+letter+"-"+(i).to_s
      axiom.append(chain1)
      axiom.append("subs")
      axiom.append(chain2)
      compoTab.append(axiom)
      @conceptList[@letter].append(chain1)
      for j in 1..maxLink-1 do
        conceptTab.append(chain1)
      end
    end
    size = size - maxLink
    size=size.ceil
    @conceptList[@letter].append(chain2)
    #fonction recursive now
    @number=@number+1
    compoTab=recursiveOnto(size,conceptTab, compoTab, 0)
    return compoTab
  end


  def roleDepth(depth, roleTab, contenu)
   


    if depth>0
      pas = depth
      content = roleDepth(depth-pas, roleTab, contenu)
    else
      content = [contenu]
    end

      role=roleTab[rand(3)]
      roleChaine= "*"+role.to_s+"."
      chain1=[roleChaine, content]
    return chain1
  end


  def recursiveOnto(size, conceptTab, compoTab, linkModif)
    axiom=[]
    miss=0
    tabPasse=[]
    if conceptTab.size < @maxLink-linkModif
    axiomeToDo = rand(conceptTab.size)+1
    else
    axiomeToDo = rand(@maxLink-linkModif)+1
    end
    conj=false
    if axiomeToDo > size
      axiomeToDo = size
    end
    chain1=""+@letter+"-"+(@number).to_s
    if @conceptList[@letter].include?(chain1)==false 
      @conceptList[@letter].append(chain1)
    end
    
    tabPasse.append(chain1)
    for i in @number..(@number+axiomeToDo-1) do
      pos=rand(conceptTab.size)
      chain2= conceptTab[pos]

      if tabPasse.include?(chain2)==true || chain1==chain2
        miss=miss+1

      else
        axiom=[]
        proba = rand(100)
        if  proba < @exp/2 && conj==true
          proba+@exp/2
        end

        if  proba < @exp/2 #axiome A & C subs B
          chain3=""+@letter+"-"+(@number+1).to_s
          axiom.append(chain1)
        axiom.append("&")
        axiom.append(chain3)
        axiom.append("subs")
        axiom.append(chain2)
        tabPasse.append(chain3)
        linkModif=1
        conj=true
        if @conceptList[@letter].include?(chain2)==false 
          @conceptList[@letter].append(chain2)
        end
        elsif  (proba >= @exp/2 && proba < @exp) #axiome R.A subs B
                            pas = @depth-(rand(@depth)+1)
          #pas = 0 #pour avoir toujours la profondeur max
          if pas>0
            content = roleDepth(pas, @roleTab, chain1)
          else
            content = [chain1]
          end

          role=@roleTab[rand(3)]
          roleChaine= "*"+role.to_s+"."
        axiom.append(roleChaine)
        axiom.append(content)
        axiom.append("subs")
        axiom.append(chain2)
          
        elsif (proba >= @exp && proba < (100-@exp)/2) #axiome A subs R.B
        pas = @depth-(rand(@depth)+1)
          if pas>0
            content = roleDepth(pas, @roleTab, chain2)
          else
            content = [chain2]
          end

          role=@roleTab[rand(3)]
          roleChaine= "*"+role.to_s+"."
        
        axiom.append(chain1)
        axiom.append("subs")
        axiom.append(roleChaine)
        axiom.append(content)

        else #axiome A subs B
        axiom.append(chain1)
        axiom.append("subs")
        axiom.append(chain2)
        
        end
        
        
        compoTab.append(axiom)
        tabPasse.append(chain2)
        size = size - 1
        
      end
    end

    for j in 1..(@maxLink-axiomeToDo+miss) do
          conceptTab.append(chain1)
    end
    if size >0
      @number=@number+1
      compoTab=recursiveOnto(size,conceptTab, compoTab, linkModif)
    end


    return compoTab

  end

end
class GenerationAns

  def initialize()
    @conj=false
  end

  def setConj(boo)
    @conj=boo
  end
  def generateAns(number, compo, depth, maxC, roleList, conceptList, roleChance)
    answerTab=[]
    
    for i in 0..number-1 do
      answer=[]
      compoLetter="A"
      for j in 0..compo-1 do
        
        answer.append("*"+compoLetter+".")
        compoTab=[]
        conceptNumber=rand(maxC+1)

        if conceptNumber==0 && i==0
           loop do
            conceptNumber=rand(maxC+1)

            break if conceptNumber!=0
          end
        end

        if conceptNumber==0
          if @conj==true
            conceptNumber=maxC
          else
            conceptNumber=rand(maxC+1)
          end
           conceptNumber=rand(maxC+1)
           if conceptNumber==0
            compoTab.append("Top")
           end
        end
        conceptRepeat=conceptList[compoLetter].map(&:clone)
        for k in 0..conceptNumber-1 do

          if rand(100) <roleChance # ajout d'un rôle
            pos=rand(conceptRepeat.length)
            concept=conceptRepeat[pos]
            conceptRepeat.delete_at(pos)
            pas = depth
          if pas>0
            content = roleDepth(pas, roleList, concept)
          else
            content = [concept]
          end
          role=roleList[rand(3)]
          roleChaine= "*"+role.to_s+"."
          compoTab.append(roleChaine)
          compoTab.append(content)

          else # ajout d'un concept
            pos=rand(conceptRepeat.length)
            compoTab.append(conceptRepeat[pos])
            conceptRepeat.delete_at(pos)
          end
          if k!=conceptNumber-1
            compoTab.append("&")
          end
          

        end
        answer.append(compoTab)
        if j!=compo-1
            answer.append("&")
        end
        compoLetter=compoLetter.succ

        
      end
      answerTab.append(answer)
    end
    return answerTab
  end
  def roleDepth(depth, roleTab, contenu)
   


    if depth>0
      pas = rand(depth)+1
      content = roleDepth(depth-pas, roleTab, contenu)
    else
      content = [contenu]
    end

      role=roleTab[rand(3)]
      roleChaine= "*"+role.to_s+"."
      chain1=[roleChaine, content]
    return chain1
  end

end



if __FILE__ == $0
require 'json'

  for numberC in 0..19 do
    numberC2=numberC



    ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=50*(j+1) #taille de l'ontologie
      exp=20 # % chance d'avoir un axiome dit "compliqué"
      composante=3 # nombre de composante
      depth=1 # profondeur maximum des roles
      maxLink=4 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Taille"+numberC2.to_s+"."+j.to_s

        
        
        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10 # nombre de réponse à générer
        maxCompo=3 # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################

      ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=200 #taille de l'ontologie
      exp=20 # % chance d'avoir un axiome dit "compliqué"
      composante=3 # nombre de composante
      depth=1 # profondeur maximum des roles
      maxLink=6 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Rep"+numberC2.to_s+"."+j.to_s

        
        
        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10*(j+1) # nombre de réponse à générer
        maxCompo=3 # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################

      ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=200 #taille de l'ontologie
      exp=20 # % chance d'avoir un axiome dit "compliqué"
      composante=3 # nombre de composante
      depth=1 # profondeur maximum des roles
      maxLink=6 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
      genFuncAns.setConj(true)
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Conj"+numberC2.to_s+"."+j.to_s

        
        
        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10 # nombre de réponse à générer
        maxCompo=1*(j+1) # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################

      ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=200 #taille de l'ontologie
      exp=10*j # % chance d'avoir un axiome dit "compliqué"
      composante=3 # nombre de composante
      depth=1 # profondeur maximum des roles
      maxLink=6 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
      genFuncAns.setConj(false)
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Comp"+numberC2.to_s+"."+j.to_s
        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10 # nombre de réponse à générer
        maxCompo=3 # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################

      ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=200 #taille de l'ontologie
      exp=20 # % chance d'avoir un axiome dit "compliqué"
      composante=1*(j+1)*2 # nombre de composante
      depth=1 # profondeur maximum des roles
      maxLink=6 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Compo"+numberC2.to_s+"."+j.to_s


        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10 # nombre de réponse à générer
        maxCompo=3 # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################

      ######################################

    # Une iteration de generation Ontologie + reponse


    genFunc=GenerationOnto.new()





    for j in 0..9

      
      size=200 #taille de l'ontologie
      exp=20 # % chance d'avoir un axiome dit "compliqué"
      composante=3 # nombre de composante
      depth=1*(j+1) # profondeur maximum des roles
      maxLink=6 # nombre d'utilisation max d'un concept dans des axiomes


      letter="A"
      comp=size/composante
      ontoTab=[]
        for i in 1..composante do


          compoTab=genFunc.generateOnto(comp, exp, composante, depth, maxLink, letter)
          letter=letter.succ

          compoTab.each { |i|
            ontoTab.append(i)
           }

        end


        fileName="Source/Prof"+numberC2.to_s+"."+j.to_s

        
        
        fileT= File.open(fileName+".txt", 'w')
        File.write(fileName+".txt", ontoTab.to_json, mode: "a")

        roleList=genFunc.getRoleTab()
        conceptList=genFunc.getConceptTab()
        fileT.close()
        #generer des propositions
        genFuncAns=GenerationAns.new()
        number=10 # nombre de réponse à générer
        maxCompo=3 # nombre maximum de concept à l'intérieur d'une composante => un gardien pour empecher que ce soit plus que le nombre de concept qu'on a dans l'onto
        roleChance=20 # chance d'avoir un role
        
        
        answerTab=genFuncAns.generateAns(number, composante, depth, maxCompo, roleList, conceptList, roleChance)
        
        

        fileTe= File.open(fileName+"-ans.txt", 'w')
        File.write(fileName+"-ans.txt", answerTab.to_json, mode: "a")

        fileTe.close()

        
    end
    #fin d'une génération d'un test
    ############################


  end # fin boucle instance de tous les tests


#######################################################








end

