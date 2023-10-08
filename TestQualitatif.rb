#!/usr/bin/env ruby
class Normalisation
	attr_accessor :counter
	def initialize()
		@counter =1
	end

	def normaRole(tab)
		result=""
		tab.each do |c|
			if c.kind_of?(Array)
				a=normaRole(c)
				a='('+a+')'
			else
				a=c.to_s
			end
			if result!=""
				if a[0]=='('
					result=result+''+a
				else
					result=result+','+a
				end 
			else
				result=a
			end
		end
		return result
	end


	def postNorm(onto)

		for c in 0.. onto.length-1 do
			nindex=onto[c].index("subs")
			newAxiom=[]
			newAxiom2=[]
			for i in 0..onto[c].length-1 do
				if (onto[c][i][0]=="*" && nindex>i && (onto[c][nindex+1].include?('R_')==false && onto[c][nindex+1].include?('Z_')==false)) # role non renommé à gauche
					if onto[c][i+1].kind_of?(Array) && onto[c][i+1].length==1
						a=onto[c][i+1]
						newConcept= 'R_'+onto[c][i].to_s+a[0]
					elsif onto[c][i+1].kind_of?(Array)
						a=normaRole(onto[c][i+1])
						newConcept= 'R_'+onto[c][i].to_s+'('+a+')'
					else 
						newConcept= 'R_'+onto[c][i].to_s+onto[c][i+1].to_s
					end
					newAxiom.append(newConcept)
					newAxiom.append("subs")
					newAxiom.append(onto[c][i])
					newAxiom.append(onto[c][i+1])
					newAxiom2.append(onto[c][i])
					newAxiom2.append(onto[c][i+1])
					newAxiom2.append("subs")
					newAxiom2.append(newConcept)
					onto[c][i]=newConcept
					if onto.include?(newAxiom)==false
						onto.append(newAxiom)
					end
					if onto.include?(newAxiom2)==false
						onto.append(newAxiom2)
					end
					onto[c].delete_at(i+1)
					break
				elsif ((onto[c][i]=="subs" ||onto[c][i]=="=") && onto[c][i+1][0]=="*" && (onto[c][0].include?('R_')==false  && onto[c][0].include?('Z_')==false)) # role non renommé à droite
					if onto[c][i+2].kind_of?(Array) && onto[c][i+2].length==1
						a=onto[c][i+2]
						newConcept= 'R_'+onto[c][i+1].to_s+a[0]
					elsif onto[c][i+2].kind_of?(Array)
						a=normaRole(onto[c][i+2])
						newConcept= 'R_'+onto[c][i+1].to_s+'('+a+')'
					else 
						newConcept= 'R_'+onto[c][i+1].to_s+onto[c][i+2].to_s
					end
					newAxiom.append(newConcept)
					newAxiom.append("subs")
					newAxiom.append(onto[c][i+1])
					newAxiom.append(onto[c][i+2])
					newAxiom2.append(onto[c][i+1])
					newAxiom2.append(onto[c][i+2])
					newAxiom2.append("subs")
					newAxiom2.append(newConcept)
					onto[c][i+1]=newConcept
					if onto.include?(newAxiom)==false
						onto.append(newAxiom)
					end
					if onto.include?(newAxiom2)==false
						onto.append(newAxiom2)
					end
						onto[c].delete_at(i+2)
					break
				end
			end
		end
	end

	def preNorm(onto)
		for i in 0..onto.length-1 do
			if onto[i].include?('=') # on a besoin de subsomption donc on remplace toutes les equivalences A = B par A subs B / B subs A
				opIndex=onto[i].index("=")
				onto[i][opIndex]="subs"
				opIndex=onto[i].index("subs")
				newAxiom=onto[i].select.with_index { |word, idx| idx > opIndex }
				newAxiom.append("subs")
				newAxiom=newAxiom+ onto[i].select.with_index { |word, idx| idx < opIndex }
				onto.append(newAxiom)
			end
		end
		norm(onto)
		postNorm(onto)
		return(onto)
	end

	def norm(onto)
		c=0
		loop do #on utilise un do while parce qu'on modifie la taille de l'onto à l'interieur de l'algorithme, en ajoutant des axiomes
		newAxiom=[]
		newAxiom2=[]

			for i in 0..onto[c].length-1 do
				#toutes les NF2 (règles selon pushing the EL enveloppe - Baader & Al 2005)
				if (onto[c][i][0]=="*" && i!=0 && onto[c].index("subs")>i && onto[c][i+2][0]=="&" ) # conjonction avec un role au milieu (NF2) il est possible qu'un des trois cas ne soit pas nécessaire
					
					
					opIndex=onto[c].index("subs")
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					newAxiom.append(onto[c][i])
					newAxiom.append(onto[c][i+1])
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					onto[c].slice!(i,3)
					opIndex=onto[c].index("subs")
					onto[c].insert(opIndex, '&')
					onto[c].insert(opIndex+1, newConcept)
					onto.append(newAxiom)
					break
				elsif (onto[c][i][0]=="*" && onto[c].index("subs")>i && onto[c][i+2]=="&") # conjonction avec un role au début (NF2) 
					
					
					opIndex=onto[c].index("subs")
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					newAxiom.append(onto[c][i])
					newAxiom.append(onto[c][i+1])
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					onto[c].slice!(0,2)
					onto[c].insert(0, newConcept)
					onto.append(newAxiom)
					break
				elsif (onto[c][i][0]=="*" && i!=0 && onto[c].index("subs")>i && onto[c][i+2]=="subs" ) # conjonction avec un role à la fin (NF2) 
					
					
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					opIndex=onto[c].index("subs")
					newAxiom.append(onto[c][i])
					newAxiom.append(onto[c][i+1])
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					onto[c].slice!(i,2)
					opIndex=onto[c].index("subs")
					onto[c].insert(opIndex, newConcept)
					onto.append(newAxiom)
					break 

				elsif ( onto[c].index("subs")>i && onto[c][i]=="&"  && onto[c][i+2]=="&" ) # conjonction de plus de 2 concepts (NF2) 
					
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					opIndex=onto[c].index("subs")
					cut=opIndex-i
					newAxiom=onto[c].slice!(i+1,cut-1)
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					opIndex=onto[c].index("subs")
					onto[c].insert(opIndex, newConcept)
					onto.append(newAxiom)
					break 


					elsif (onto[c][i][0]=="*" && onto[c].index("subs")>i && onto[c][i+1].kind_of?(Array) && onto[c][i+1].length>1) # role seul à gauche mais contenu non atomique (NF3) 
					
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					onto[c][i+1].each do |n|
						newAxiom.append(n)
					end
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					onto[c][i+1]=[newConcept]
					onto.append(newAxiom)
					break 	



				elsif (onto[c][0][0]=='*' && onto[c][3][0]=='*'  && onto[c][2]=='subs'  && onto[c].length==5) # subsomption de deux roles (NF5)
					
					opIndex=onto[c].index("subs")
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					newAxiom.append(newConcept)
					newAxiom.append("subs")
					newAxiom.append(onto[c][3])
					newAxiom.append(onto[c][4])
					onto[c].delete_at(4)
					onto[c][3]=newConcept
					onto.append(newAxiom)

					break

				elsif (onto[c][0][0]=='*' && onto[c][2]=='subs' && onto[c].length>4) # subsomption d'un rôle et d'une conjonction à droite
					opIndex=onto[c].index("subs")
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					
					
					newAxiom.append(onto[c][0])
					newAxiom.append(onto[c][1])
					newAxiom.append("subs")
					newAxiom.append(newConcept)
					onto[c].delete_at(0)
					onto[c][0]=newConcept
					onto.append(newAxiom)
					break
				




				elsif ((onto[c][i]=="subs" && onto[c][i+1][0]=="*" && onto[c][i+2].kind_of?(Array)) && onto[c][i+2].length>1 &&  onto[c][i+2].length!=1) # (NF6) 'role complexe a droite'
					newConcept= 'X_'+@counter.to_s
					@counter=@counter+1
					newAxiom.append(newConcept)
					newAxiom.append("subs")
					onto[c][i+2].each do |n|
						newAxiom.append(n)
					end
					onto[c][i+2]=[newConcept]
					onto.append(newAxiom)
					break

				



				elsif (onto[c][i]=="subs" && (onto[c][i+2]=='&' || onto[c][i+3]=='&')) # conjonction a droite (NF7) 
					
					remaining=onto[c].length-i
					if onto[c][i+2]=='&'
						aDiviser=onto[c].slice!(i+2,remaining)
					else
						aDiviser=onto[c].slice!(i+3,remaining)
					end
					aDiviser.delete_at(0)
					j=0
					loop do # plutôt que de refaire un passage pour chaque membre de la conjonction, une boucle ici permet de completement "vider" la conjonction de ses concepts
						if (aDiviser[j]!="&" && aDiviser[j][0]=="*") #si c'est un rôle (on a alors besoin de prendre le concept/tableau qui suit)
							newAxiom=[]
							if onto[c][1]=="&"
								newAxiom.append(onto[c][0])
								newAxiom.append(onto[c][1])
								newAxiom.append(onto[c][2])
							elsif onto[c][0][0]=="*"
								newAxiom.append(onto[c][0])
								newAxiom.append(onto[c][1])
							else
								newAxiom.append(onto[c][0])
							end
							newAxiom.append("subs")
							newAxiom.append(aDiviser[j])
							newAxiom.append(aDiviser[j+1])
							onto.append(newAxiom)
							j=j+2
						elsif (aDiviser[j]!="&")
							newAxiom=[]
							if onto[c][1]=="&"
								newAxiom.append(onto[c][0])
								newAxiom.append(onto[c][1])
								newAxiom.append(onto[c][2])
							elsif onto[c][0][0]=="*"
								newAxiom.append(onto[c][0])
								newAxiom.append(onto[c][1])
							else
								newAxiom.append(onto[c][0])
							end
							newAxiom.append("subs")
							newAxiom.append(aDiviser[j])
							onto.append(newAxiom)
							j=j+1
						else 
							j=j+1
						end
					break if j > aDiviser.length-1
					end
					break  



				elsif i==onto[c].length-1 #si l'axiom est ok

					c=c+1
					break
				end
			end
		break if c>=onto.length
		end

		return onto
	end

end


class Classification
	def initialize()
		@reverse=Hash.new("void")
		@ontoIni=[]
		@classiIni=Hash.new("void")
	end

	def setOntoIni(tab)
		@ontoIni=tab.map(&:clone)
	end

	def setClassiIni(hashClass)
		@classiIni=Marshal.load(Marshal.dump(hashClass))
	end

	#la fonction prends en entrée une ontologie et prépare dans un Hash l'initialisation de la classification (cad chaque concept est present dans le hash sous la forme "A=>{A}")
	def ontoHash(onto) 
		hashing=Hash.new("void")
		testH=Hash.new("void")
		onto.each { |o|

			if hashing[o[0]]=="void" # on verifie que le concept n'est pas deja dans le hash
				if o[0][0]!="*"
					hashTemp={o[0] => [o[0]]}
					hashing=hashing.merge(hashTemp)
				end
			end
			if o[1]=='subs'
				if hashing[o[2]]=="void" && o[2][0]!="*"
					hashTemp={o[2] => [o[2]]}
					hashing=hashing.merge(hashTemp)
				end
			end
			if o[1]=='&'
				if hashing[o[2]]=="void" && o[2][0]!="*"
					hashTemp={o[2] => [o[2]]}
					hashing=hashing.merge(hashTemp)
				end
				if hashing[o[4]]=="void" && o[4][0]!="*"
					hashTemp={o[4] => [o[4]]}
					hashing=hashing.merge(hashTemp)
				end
			end
			if o[0][0]=="*" # on recupère aussi les concepts à l'interieur des rôles
				if o[1].kind_of?(Array) && o[1].length==1
					a=o[1][0]
				else
					a=o[1]
				end
				if hashing[a]=="void"
					hashTemp={a => [a]}
					hashing=hashing.merge(hashTemp)
				end
			end
			if o[2][0]=="*"
				if o[3].kind_of?(Array) && o[3].length==1
					a=o[3][0]
				else
					a=o[3]
				end
				if hashing[o[3]]=="void"
					hashTemp={a => [a]}
					hashing=hashing.merge(hashTemp)
				end
			end
		}
		hashing2={"role" => testH}
		hashing=hashing.merge(hashing2)

		return hashing

	end 


	# La fonction permet d'ajouter à un hashing existant les concepts qui ont été ajoutés pendant le fup/normalisation diverse. Il y a moins de cas car ces ajouts sont toujours de la même forme.
	def ontoHashFup(onto, hashing)

		onto.each { |o|

			if hashing[o[0]]=="void"
				if o[0][0]!="*"
					hashTemp={o[0] => [o[0]]}
					hashing=hashing.merge(hashTemp)
				end
			end
			if o[1]=='&' 
				if hashing[o[2]]=="void"
					hashTemp={o[2] => [o[2]]}
					hashing=hashing.merge(hashTemp)
				end
				if hashing[o[4]]=="void"
					hashTemp={o[4] => [o[4]]}
					hashing=hashing.merge(hashTemp)
				end
			end

			if o[1]=="subs"
				if o[2][0]!="*"
					if hashing[o[2]]=="void"
						hashTemp={o[2] => [o[2]]}
						hashing=hashing.merge(hashTemp)
					end
				else
					if hashing[o[3][0]]=="void"
						hashTemp={o[3][0] => [o[3][0]]}
						hashing=hashing.merge(hashTemp)
					end

				end
			end
		}
		return hashing
	end
	#classification selon Baader & Al 2005
	def classiBaader(onto, classi) 
		modifiedTab=[]
		i=0
		
		reverse=Marshal.load(Marshal.dump(@reverse))

		loop do 

			if onto[i][1]=="subs"
				if onto[i][2][0]=="*"
					classiTemp=classi["role"][onto[i][2]] #CR3 (a)
					if classiTemp=="void"
						tabInter=[]
						tabInter.append(onto[i][0].to_s)
						if onto[i][3].kind_of?(Array) && onto[i][3].length==1
							a=onto[i][3]
							tabInter.append(a[0])
						else 
							tabInter.append(onto[i][3].to_s)
						end
						classiTemp={onto[i][2] => [tabInter]}
						classi["role"]=classi["role"].merge(classiTemp)
					else
						if(classi["role"][onto[i][2]].include?([onto[i][0],onto[i][3]])==false)
							tabTemp=classi["role"][onto[i][2]]
							tabInter=[]
							tabInter.append(onto[i][0].to_s)
							if onto[i][3].kind_of?(Array) && onto[i][3].length==1
								a=onto[i][3]
								tabInter.append(a[0])
							else 
								tabInter.append(onto[i][3].to_s)
							end
							tabTemp=tabTemp.append(tabInter)
							classiTemp={onto[i][2] => tabTemp}
							classi["role"]=classi["role"].merge(classiTemp)
						end
					end
					onto.delete_at(i)
				elsif  (onto[i][0][0]!="*" &&  classi[onto[i][0]].include?(onto[i][2])==false) #CR1 (a)
					tabTemp=classi[onto[i][0]]
					tabTemp=tabTemp.append(onto[i][2])
					if reverse[onto[i][2]]=="void"
						reverse[onto[i][2]]=[]
					end
					reverse[onto[i][2]].append(onto[i][0])
					classiTemp={onto[i][0] => tabTemp}
					classi=classi.merge(classiTemp)
					onto.delete_at(i)
				else #suppression des redondances
					if (onto[i][0][0]!="*" &&  classi[onto[i][0]].include?(onto[i][2])==true)
						onto.delete_at(i)
					else
						i=i+1;  
					end
				end
			else
				i=i+1;
			end

		break if i>=onto.length
		end
		modifiedTab=[]
		classi.each_key do |key|
			if key!="role"
				modifiedTab.append(key)
			end
			if reverse[key]=="void"
				reverse[key]=[]
			end
		end
		modifiedTemp = modifiedTab.map(&:clone)
		@countertest=0

		# fin de la première itération qui fait toutes les CR1 (a) et CR3 (a)
		# On parcourt maintenant une fois la classification dans son ensemble, puis uniquement les ensembles qui ont été modifiés


		while modifiedTemp.length!=0 do
			modifiedTab=[]
			modifiedTemp.each do |modifiedCR|
				reverse[modifiedCR].each do |subToCheck| # CR1 : on a ajouté quelque chose à modifiedCR, donc on repercute dans tous les ensembles où il est present.
					@countertest=@countertest+1
					for i in 0..classi[modifiedCR].length-1 do
						if classi[subToCheck].include?(classi[modifiedCR][i])==false
							if classi[subToCheck]=="void"
								classi[subToCheck]=[]
							end
							classi[subToCheck].append(classi[modifiedCR][i])
							if modifiedTab.include?(subToCheck)==false
								modifiedTab.append(subToCheck)
							end
							if reverse[classi[modifiedCR][i]].include?(subToCheck)==false
								if reverse[classi[modifiedCR][i]]=="void"
									reverse[classi[modifiedCR][i]]=[]
								end
								reverse[classi[modifiedCR][i]].append(subToCheck)
							end
						end
					end
				end
				onto.each do |axiom| 
					if (classi[modifiedCR].include?(axiom[0]) && axiom[1]=="&" && classi[modifiedCR].include?(axiom[2]) && classi[modifiedCR].include?(axiom[4])==false ) #CR2
						classi[modifiedCR].append(axiom[4])
						if modifiedTab.include?(modifiedCR)==false
							modifiedTab.append(modifiedCR)
						end
						if modifiedTab.include?(axiom[4])==false
							modifiedTab.append(axiom[4])
						end
						if reverse[axiom[4]].include?(modifiedCR)==false
							if reverse[axiom[4]]=="void"
								reverse[axiom[4]]=[]
							end
							reverse[axiom[4]].append(modifiedCR)
						end
					elsif axiom[0][0]=='*' && classi[modifiedCR].include?(axiom[1][0])==true   #CR4
						classi["role"][axiom[0]].each do |couple|
							if couple[1]==modifiedCR && classi[couple[0]].include?(axiom[3])==false
								classi[couple[0]].append(axiom[3])
								if modifiedTab.include?(couple[0])==false
									modifiedTab.append(couple[0])
								end
								if modifiedTab.include?(axiom[3])==false
									modifiedTab.append(axiom[3])
								end
								if reverse[axiom[3]].include?(couple[0])==false
									if reverse[axiom[3]]=="void"
										reverse[axiom[3]]=[]
									end
									reverse[axiom[3]].append(couple[0])
								end
							end
						end
					end
				end
			end
		modifiedTemp = modifiedTab.map(&:clone)
		end #while

		@reverse=Marshal.load(Marshal.dump(reverse))
		@onto=onto.map(&:clone)
		return classi  
	end #end function


	# Comparaison des relations de subsomptions entre rest ou miss, la fonction est similaire à classiBaader mais utilise d'autres entrées.
	# On pourrait factoriser toutes les fonctions de classification
	def classiBaaderMissRest(query, answer, normB) 

		modifiedTab=[]
		onto2=[]
		i=0
		reverse=Marshal.load(Marshal.dump(@reverse))
		classi=Marshal.load(Marshal.dump(@classiIni))
		onto=@ontoIni.map(&:clone)
		newAxiom1=['Query', 'subs'] 
		newAxiom2=[]
		query.each do |c|
			newAxiom1.append(c)
			newAxiom2.append(c)
		end
		newAxiom2.append('subs')
		newAxiom2.append('Query')
		onto2.append(newAxiom1)
		onto2.append(newAxiom2)
		newAxiom1=['Answer', 'subs']
		newAxiom2=[]
		answer.each do |c|
			newAxiom1.append(c)
			newAxiom2.append(c)
		end
		newAxiom2.append('subs')
		newAxiom2.append('Answer')
		onto2.append(newAxiom1)
		onto2.append(newAxiom2)
		modifiedTab.append("Query")
		modifiedTab.append("Answer")
		if reverse["Answer"]=="void"
			reverse["Answer"]=[]
		end
		if reverse["Query"]=="void"
			reverse["Query"]=[]
		end
		onto2=normB.preNorm(onto2)
		classi=ontoHashFup(onto2, classi)

		onto2.each do |axiom|
			axiom.flatten
			axiom.each do |c|
				if modifiedTab.include?(c)==false  && c!="&" && c[0]!="*" && c!="subs"
					if c.kind_of?(Array)
						temp=c[0]
					else
						temp=c
					end
					classi[temp].each do |d|
						if modifiedTab.include?(d)==false
							modifiedTab.append(d)
						end
					end
				end
				if reverse[c]=="void"  && c!="&"  && c[0]!="*" && c!="subs"
					classi[temp].each do |d|
						if reverse[d]=="void"
							reverse[d]=[]
						end
					end
				end
			end
		end
		modifiedTab.each do |toFind|
			classi.each_key do |set|
				if classi[set].include?(toFind) && modifiedTab.include?(set)==false
					modifiedTab.append(set)
				end
			end
		end

		loop do 
			if onto2[i][1]=="subs"
				if onto2[i][2][0]=="*"
					classiTemp=classi["role"][onto2[i][2]] #CR3
					if classiTemp=="void"
						tabInter=[]
						tabInter.append(onto2[i][0].to_s)
						if onto2[i][3].kind_of?(Array) && onto2[i][3].length==1
							a=onto2[i][3]
							tabInter.append(a[0])
						else 
							tabInter.append(onto2[i][3].to_s)
						end
						classiTemp={onto2[i][2] => [tabInter]}
						classi["role"]=classi["role"].merge(classiTemp)
					else
						if(classi["role"][onto2[i][2]].include?([onto2[i][0],onto2[i][3]])==false)
							tabTemp=classi["role"][onto2[i][2]]
							tabInter=[]
							tabInter.append(onto2[i][0].to_s)
							if onto2[i][3].kind_of?(Array) && onto2[i][3].length==1
								a=onto2[i][3]
								tabInter.append(a[0])
							else 
								tabInter.append(onto2[i][3].to_s)
							end
							tabTemp=tabTemp.append(tabInter)
							classiTemp={onto2[i][2] => tabTemp}
							classi["role"]=classi["role"].merge(classiTemp)
						end
					end
					onto2.delete_at(i)
				elsif  (onto2[i][0][0]!="*" &&  classi[onto2[i][0]].include?(onto2[i][2])==false) #CR1
					tabTemp=classi[onto2[i][0]]
					tabTemp=tabTemp.append(onto2[i][2])
					if reverse[onto2[i][2]]=="void"
						reverse[onto2[i][2]]=[]
					end
					reverse[onto2[i][2]].append(onto2[i][0])
					classiTemp={onto2[i][0] => tabTemp}
					classi=classi.merge(classiTemp)
					onto2.delete_at(i)
				else #suppression des redondances
					if (onto2[i][0][0]!="*" &&  classi[onto2[i][0]].include?(onto2[i][2])==true)
						onto2.delete_at(i)
					else
						i=i+1;  
					end
				end
			else
				i=i+1;
			end

		break if i>=onto2.length
		end

		onto2.each do |axiom|
			onto.append(axiom)
		end

		modifiedTemp = modifiedTab.map(&:clone)
		while modifiedTemp.length!=0 do
			modifiedTab=[]
			modifiedTemp.each do |modifiedCR|
				reverse[modifiedCR].each do |subToCheck| # CR1 : on a ajouté quelque chose à modifiedCR, donc on repercute dans tous les ensembles où il est present.
					@countertest=@countertest+1
					for i in 0..classi[modifiedCR].length-1 do
						if classi[subToCheck].include?(classi[modifiedCR][i])==false
							if classi[subToCheck]=="void"
								classi[subToCheck]=[]
							end
								classi[subToCheck].append(classi[modifiedCR][i])
							if modifiedTab.include?(subToCheck)==false
								modifiedTab.append(subToCheck)
							end
							if reverse[classi[modifiedCR][i]].include?(subToCheck)==false
								if reverse[classi[modifiedCR][i]]=="void"
									reverse[classi[modifiedCR][i]]=[]
								end
								reverse[classi[modifiedCR][i]].append(subToCheck)
							end
						end
					end
				end
				onto.each do |axiom| 
					if (classi[modifiedCR].include?(axiom[0]) && axiom[1]=="&" && classi[modifiedCR].include?(axiom[2]) && classi[modifiedCR].include?(axiom[4])==false ) #CR2
						classi[modifiedCR].append(axiom[4])
						if modifiedTab.include?(modifiedCR)==false
							modifiedTab.append(modifiedCR)
						end
						if modifiedTab.include?(axiom[4])==false
							modifiedTab.append(axiom[4])
						end
						if reverse[axiom[4]].include?(modifiedCR)==false
							if reverse[axiom[4]]=="void"		
								reverse[axiom[4]]=[]
							end
							reverse[axiom[4]].append(modifiedCR)
						end
					elsif axiom[0][0]=='*' && classi[modifiedCR].include?(axiom[1][0])==true#CR4
						classi["role"][axiom[0]].each do |couple|
							if couple[1]==modifiedCR && classi[couple[0]].include?(axiom[3])==false
								classi[couple[0]].append(axiom[3])
							if modifiedTab.include?(couple[0])==false
								modifiedTab.append(couple[0])
							end
							if modifiedTab.include?(axiom[3])==false
								modifiedTab.append(axiom[3])
							end
							if reverse[axiom[3]].include?(couple[0])==false
								if reverse[axiom[3]]=="void"
								reverse[axiom[3]]=[]
								end
								reverse[axiom[3]].append(couple[0])
							end
						end
					end
				end
			end
		end
		modifiedTemp = modifiedTab.map(&:clone)
	end #while

	return classi  
	end #end function


	# Comparaison des relations de subsomptions entre rest ou miss, la fonction est similaire à classiBaader mais utilise d'autres entrées.
	# On pourrait factoriser toutes les fonctions de classification
	def classiBaaderComp(classiAFaire, query, answer, normB) 
		modifiedTab=[]
		onto2=[]
		i=0
		reverse=Marshal.load(Marshal.dump(@reverse))
		classi=Marshal.load(Marshal.dump(classiAFaire))
		onto=@onto.map(&:clone)
		newAxiom1=['Query', 'subs'] 
		newAxiom2=[]
		query.each do |c|
			newAxiom1.append(c)
			newAxiom2.append(c)
		end
		newAxiom2.append('subs')
		newAxiom2.append('Query')
		onto2.append(newAxiom1)
		onto2.append(newAxiom2)
		newAxiom1=['Answer', 'subs']
		newAxiom2=[]
		answer.each do |c|
			newAxiom1.append(c)
			newAxiom2.append(c)
		end
		newAxiom2.append('subs')
		newAxiom2.append('Answer')
		onto2.append(newAxiom1)
		onto2.append(newAxiom2)
		modifiedTab.append("Query")
		modifiedTab.append("Answer")
		if reverse["Answer"]=="void"
			reverse["Answer"]=[]
		end
		if reverse["Query"]=="void"
			reverse["Query"]=[]
		end
		onto2=normB.preNorm(onto2)
		classi=ontoHashFup(onto2, classi)

		onto2.each do |axiom|
			axiom.flatten
			axiom.each do |c|
				if modifiedTab.include?(c)==false  && c!="&" && c[0]!="*" && c!="subs"
					if c.kind_of?(Array)
						temp=c[0]
					else
						temp=c
					end
					classi[temp].each do |d|
						if modifiedTab.include?(d)==false
							modifiedTab.append(d)
						end
					end
				end
				if reverse[c]=="void"  && c!="&"  && c[0]!="*" && c!="subs"
					classi[temp].each do |d|
						if reverse[d]=="void"
							reverse[d]=[]
						end
					end
				end
			end
		end
		modifiedTab.each do |toFind|
			classi.each_key do |set|
				if classi[set].include?(toFind) && modifiedTab.include?(set)==false
					modifiedTab.append(set)
				end
			end
		end

		loop do 
			if onto2[i][1]=="subs"
				if onto2[i][2][0]=="*"
					classiTemp=classi["role"][onto2[i][2]] #CR3
					if classiTemp=="void"
						tabInter=[]
						tabInter.append(onto2[i][0].to_s)
						if onto2[i][3].kind_of?(Array) && onto2[i][3].length==1
							a=onto2[i][3]
							tabInter.append(a[0])
						else 
							tabInter.append(onto2[i][3].to_s)
						end
						classiTemp={onto2[i][2] => [tabInter]}
						classi["role"]=classi["role"].merge(classiTemp)
					else
						if(classi["role"][onto2[i][2]].include?([onto2[i][0],onto2[i][3]])==false)
							tabTemp=classi["role"][onto2[i][2]]
							tabInter=[]
							tabInter.append(onto2[i][0].to_s)
							if onto2[i][3].kind_of?(Array) && onto2[i][3].length==1
								a=onto2[i][3]
								tabInter.append(a[0])
							else 
								tabInter.append(onto2[i][3].to_s)
							end
							tabTemp=tabTemp.append(tabInter)
							classiTemp={onto2[i][2] => tabTemp}
							classi["role"]=classi["role"].merge(classiTemp)
						end
					end
					onto2.delete_at(i)
				elsif  (onto2[i][0][0]!="*" &&  classi[onto2[i][0]].include?(onto2[i][2])==false) #CR1
					tabTemp=classi[onto2[i][0]]
					tabTemp=tabTemp.append(onto2[i][2])
					if reverse[onto2[i][2]]=="void"
						reverse[onto2[i][2]]=[]
					end
					reverse[onto2[i][2]].append(onto2[i][0])
					classiTemp={onto2[i][0] => tabTemp}
					classi=classi.merge(classiTemp)
					onto2.delete_at(i)
				else #suppression des redondances
					if (onto2[i][0][0]!="*" &&  classi[onto2[i][0]].include?(onto2[i][2])==true)
						onto2.delete_at(i)
					else
						i=i+1;  
					end
				end
			else
				i=i+1;
			end

		break if i>=onto2.length
		end

		onto2.each do |axiom|
			onto.append(axiom)
		end

		modifiedTemp = modifiedTab.map(&:clone)
		while modifiedTemp.length!=0 do
			modifiedTab=[]
			modifiedTemp.each do |modifiedCR|
				reverse[modifiedCR].each do |subToCheck| # CR1 : on a ajouté quelque chose à modifiedCR, donc on repercute dans tous les ensembles où il est present.
					@countertest=@countertest+1
					for i in 0..classi[modifiedCR].length-1 do
						if classi[subToCheck].include?(classi[modifiedCR][i])==false
							if classi[subToCheck]=="void"
								classi[subToCheck]=[]
							end
								classi[subToCheck].append(classi[modifiedCR][i])
							if modifiedTab.include?(subToCheck)==false
								modifiedTab.append(subToCheck)
							end
							if reverse[classi[modifiedCR][i]].include?(subToCheck)==false
								if reverse[classi[modifiedCR][i]]=="void"
									reverse[classi[modifiedCR][i]]=[]
								end
								reverse[classi[modifiedCR][i]].append(subToCheck)
							end
						end
					end
				end
				onto.each do |axiom| 
					if (classi[modifiedCR].include?(axiom[0]) && axiom[1]=="&" && classi[modifiedCR].include?(axiom[2]) && classi[modifiedCR].include?(axiom[4])==false ) #CR2
						classi[modifiedCR].append(axiom[4])
						if modifiedTab.include?(modifiedCR)==false
							modifiedTab.append(modifiedCR)
						end
						if modifiedTab.include?(axiom[4])==false
							modifiedTab.append(axiom[4])
						end
						if reverse[axiom[4]].include?(modifiedCR)==false
							if reverse[axiom[4]]=="void"		
								reverse[axiom[4]]=[]
							end
							reverse[axiom[4]].append(modifiedCR)
						end
					elsif axiom[0][0]=='*' && classi[modifiedCR].include?(axiom[1][0])==true#CR4
						classi["role"][axiom[0]].each do |couple|
							if couple[1]==modifiedCR && classi[couple[0]].include?(axiom[3])==false
								classi[couple[0]].append(axiom[3])
							if modifiedTab.include?(couple[0])==false
								modifiedTab.append(couple[0])
							end
							if modifiedTab.include?(axiom[3])==false
								modifiedTab.append(axiom[3])
							end
							if reverse[axiom[3]].include?(couple[0])==false
								if reverse[axiom[3]]=="void"
								reverse[axiom[3]]=[]
								end
								reverse[axiom[3]].append(couple[0])
							end
						end
					end
				end
			end
		end
		modifiedTemp = modifiedTab.map(&:clone)
	end #while

	return classi  
	end #end function
end #End class


class FillUP
	def initialize()
		@counter1=1
		@counter2=1
	end

	def setNamePrefix(string)
		@prefix=string
	end

	def setCompoSuffix(string)
		@suffix=string
	end

	def returnClassi()
		return @classi
	end


	# Prepare le concept pour le fill-up en renommant les rôles et le concept lui même
	def preFup(onto, classi, desc, funcBaader,funcClassi)
		@onto=onto
		@classi=classi
		hashingRole=Hash.new("void")
		i=0

		loop do
			if desc[i][0]=="*"
				if desc[i+1].length==1
					a=desc[i+1]
					newConcept= 'R_'+desc[i].to_s+a[0] 


					tabTemp=[desc[i], desc[i+1]]
					roleTemp={newConcept => tabTemp}           
					hashingRole=hashingRole.merge(roleTemp)

					newAxiom1=[newConcept, 'subs', desc[i], desc[i+1]]
					newAxiom2=[desc[i], desc[i+1], 'subs', newConcept]

					desc[i]=newConcept
					desc.delete_at(i+1)
					onto.append(newAxiom2)
					onto.append(newAxiom1)
				else
					newConcept= 'Z_'+desc[i]+@counter1.to_s
					@counter1=@counter1+1
					tabTemp=[desc[i], desc[i+1]]
					roleTemp={newConcept => tabTemp}           
					hashingRole=hashingRole.merge(roleTemp)

					newAxiom1=[newConcept, 'subs', desc[i], desc[i+1]]
					newAxiom2=[desc[i], desc[i+1], 'subs', newConcept]

					desc[i]=newConcept
					desc.delete_at(i+1)
					onto.append(newAxiom2)
					onto.append(newAxiom1)

				end
			else
				i=i+1
			end
			break if i>desc.length-1
		end

		newConcept=@prefix+'_'+@suffix
		@prefix="F"
		
		newAxiom1=[newConcept, 'subs']
		newAxiom2=[]
		if desc.kind_of?(Array)
			desc.each do |c|
				newAxiom1.append(c)
				newAxiom2.append(c)
			end
		else
			newAxiom1.append(desc)
			newAxiom2.append(desc)
		end 

		newAxiom2.append('subs')
		newAxiom2.append(newConcept)

		onto.append(newAxiom2)
		onto.append(newAxiom1)


		onto=funcBaader.preNorm(onto) 

		classi=funcClassi.ontoHashFup(onto, classi) 
		classi=funcClassi.classiBaader(onto, classi)
		@classi=classi
		result=fup(onto, classi, newConcept, funcBaader, funcClassi, hashingRole)
		result=fupCleanUp(result)

		return result
	end


		def fup(onto, classi, desc, funcBaader, funcClassi,hashingRole)
		# R_ => role norma dans onto baader (pour fup)
		# F_ => descri norma dans fup
		# X_ => concept norma dans onto Baader (pour baader)
		# Z_ => role norma dans fup

		newDesc=[]

		if classi[desc]!="void"

			classi[desc].each do |c|
	
				if newDesc.length!=0
					newDesc.append('&')
				end
				if (c[0]=='Z' &&  c[1]=='_')

					contenu=hashingRole[c]

					newDesc.append(c)

					if contenu!="void"
					newDesc.append('&')
					newDesc.append(contenu[0])
					end
					if contenu[1].kind_of?(Array) # on ajoute un suffixe
						setCompoSuffix(@counter2.to_s)
						@counter2=@counter2+1
						setNamePrefix="F_"

						resultInter=preFup(onto, classi, contenu[1], funcBaader, funcClassi)
						newDesc.append(resultInter)

					else #a priori inutile car tous les concepts suivants une restriction existentielle est dans un tableau

						resultInter=classi[contenu[1]]
						tabInter=[]
						if resultInter!='void'
							
							resultInter.each do |ri|

								if tabInter.length!=0

									tabInter.append('&') 
								end
								tabInter.append(ri)
							end
							newDesc.append(tabInter)
						else
							#rien
						end
					end
				elsif (c[0]=='R' &&  c[1]=='_')
	
					role = c[c[2..c.index(".")]]
					contenu = c[c.index(".")+1, c.length-1]

					testF=fup(onto, classi, contenu, funcBaader, funcClassi,hashingRole)
					

					rolePos=[]
					rolePos= newDesc.each_index.select { |index| newDesc[index] == role} # toutes les positions où on trouve le role d'une restriction existentielle, pour vérifier si on a pas déjà son contenu quelque part et éviter les redondances

					if rolePos.length>0
						merged=false
						i=0
						loop do
							contenuAmerge= newDesc[rolePos[i]+1]
							toMerge=roleMergeFup(contenuAmerge, testF)
							if toMerge==1
								merged=true
							end
							i=i+1
						break if merged==true || i>=rolePos.length
						end 
						if merged==false
							newDesc.append(role)
							newDesc.append(testF)
						else
							newDesc.delete_at(newDesc.length-1)
						end
					else

					newDesc.append(role)
					newDesc.append(testF)
					end
				else
					if newDesc.include?(c)==false
					newDesc.append(c)
					else
						newDesc.delete_at(newDesc.length-1)
					end


				end
			end
		else
			newDesc=desc
		end

		return newDesc
	end

		# compare deux contenus de restriction existentielle
    	def roleMergeFup(tab, newContenu)
		roleMerge=false
		fin=0
		newContenu.each do |a|
			if a!='&' && tab.include?(a)==true
				# puts "present"
			elsif a!='&' && a.kind_of?(Array) 

				role=newContenu[newContenu.index(a)-1]
				
				rolePos=[]
				rolePos= newContenu.each_index.select { |index| newContenu[index] == role}
				i=0
				loop do
					contenuAmerge= newContenu[rolePos[i]+1]
					fin==roleMergeFup(contenuAmerge, a)
					if fin==1
						return fin
					end
				i=i+1	
				break if i>=rolePos.length
				end
			else 
				fin=1
			 return fin
			end
			
		end
		return fin
    end

    # retire les concepts qui n'étaient pas dans la TBox initiale et les & superflus
	def fupCleanUp(desc)
		i=0
		loop do 

			if desc[i]=="&"
				if i==0
					desc.delete_at(0)
				elsif desc[i-1]=="&"
					desc.delete_at(i)
				else
					i=i+1
				end
			elsif desc[i][1]=="_"
				desc.delete_at(i) 
			elsif desc[i][0]=="*"
				if desc[i+1]==["Top"] && desc[i+1].length>1
					desc.delete_at(i)
					desc.delete_at(i)
				else
					i=i+1
				end
			elsif desc[i].kind_of?(Array)
				desc[i]=fupCleanUp(desc[i])
				if desc[i].length==0
					desc.delete_at(i)
					desc.delete_at(i-1)
				end
				i=i+1
			else  
				i=i+1
			end
		break if i>desc.length-1
		end
		loop do
			if desc[desc.length-1]=='&'


				desc.delete_at(desc.length-1)
			end
			if desc[0]=='&'

				desc.delete_at(0)
			end
		break if desc[desc.length-1]!='&' && desc[0]!="&"

		end
			return desc
	end
end


class TSO


	def tso(minu, subtr)
    i=0
    if minu.kind_of?(Array) && minu!="&"
    		min = minu.map(&:clone)
    else
    		min=minu
    end

    if subtr.kind_of?(Array) && minu!="&"
    		subt = subtr.map(&:clone)
    else
    		subt=subtr
    end
    
    loop do
      if min[i]!='&'
        if min[i][0]=="*"
          if subt.include?(min[i]) # S'il existe un rôle identique dans subt, on fait le TSO du contenu
            loc=subt.index(min[i])
            temp=tso(min[i+1], subt[loc+1])
            if temp.length==1 && temp[0]=='Top' # si le resultat du TSO est top, on peut retirer le rôle et son contenu dans son ensemble
              min.delete_at(i)
              min.delete_at(i)
            else
              min[i+1]=temp
              i=i+2    
            end

          else
            i=i+2
          end


        else
          if subt.include?(min[i])
            if min.kind_of?(Array) 
              min.delete_at(i)
            else
              min='Top'
            end

            if i!=min.length-1 #si c'est pas la fin, on retire le '&' qui suivait le concept supprimé juste avant
              if min.kind_of?(Array)  
                min.delete_at(i)
              else
                min=['Top']
              end
            end
          else
            i=i+2
          end
        end
      else #si on est dans un &
        i=i+1
      end
    break if i>min.length-1
    end



    if min.length==0
      min=['Top']
    end
    min=tsoCleanup(min)

  
  return min
  end



 def tsoCleanup(min)

  	    # nettoyage des '&'
    i=0
    loop do

    if (min[i]=='&' && (i==0 && min.length-1==0))
    		min=["Top"]
    elsif (min[i]=='&' && (i==0 || i==min.length-1))
		min.delete_at(i)
    elsif (min[i]=='&' && i!=min.length-1)
    	if min[i+1]=='&'
    		min.delete_at(i)
    	else
    		i=i+1
    	end
    elsif (min[i]=='&' && i!=0)
    	if min[i-1]=='&'
    		min.delete_at(i)
    	else
    		i=i+1
    	end	
    elsif (min[i].length>=2)

    	if min[i][1]=='_'
    		if i!=0
    			min.delete_at(i-1)
    			min.delete_at(i-1)
    		else
    			min.delete_at(i)
    		end
    		
    	else
    		i=i+1
    	end
    elsif min[i].kind_of?(Array) 
    	min[i]=tsoCleanup(min[i])
    	i=i+1
    else
    	i=i+1
    end
    	

    break if i>min.length-1
    end

   if min.length==0
      min=['Top']
    end



  	return min
  end

end



class CCO

  def initialize(tempFonc, comp)
    @comp=comp
    @compSub=Hash.new("void")
    @compSub2=Hash.new("void")
    @tso=TSO.new
    @compteurCompa=0
    @compteurDiff=0
    @compteurSub=0
	@tempFonc=tempFonc
    @fupDemande=[]
    @fupReponse=Hash.new("void")
  end


  def setFupDemande(tab)
  	@fupDemande=tab.map(&:clone)
  end

  def setFupReponse(hashRep)
  	@fupReponse=Marshal.load(Marshal.dump(hashRep))
  end

  def getCompa()
  	return @compteurCompa
  end

  def getDiff()
  	return @compteurDiff
  end

    def getSub()
  	return @compteurSub
  end


  # determination des relations de subsomption entre réponses et demande à l'aide de la classification obtenue lors du calcul des fill-up
  def componentComparison(onto, hashC, query, answerList, normB, classi, fuP) 

    	
	    @classi=Marshal.load(Marshal.dump(hashC))
	    @funcBaad=normB
	    @funcClass=classi
	    @answerList=answerList


	    @comp.each do |c|
	      hashComp={c=>[]}
	      if query.include?(c)
	      	cIndex2=query.index(c)
	      	queryComp= query[cIndex2+1]
	        answerList.each_key do |a|

	          if answerList[a].include?(c)  #answer have the component, we need to see if it subs or not the query
	            cIndex=answerList[a].index(c)
	            answerComp= answerList[a][cIndex+1]
	            if answerComp.include?("Top")==false && queryComp.include?("Top")==false

	    		  	if @classi[a.to_s+"_"+c.to_s].include?("Q_"+c.to_s) && @classi["Q_"+c.to_s].include?(a.to_s+"_"+c.to_s)

	    		  		res="equiv"
	    		  	elsif @classi[a.to_s+"_"+c.to_s].include?("Q_"+c.to_s)

	    		  		res="subsuming"
	    		  	elsif @classi["Q_"+c.to_s].include?(a.to_s+"_"+c.to_s)
	    		  		res="subsumed"

	    		  	else
	    		  		res="nr"
	    		  	end
	    		  		
	              hashComp[c].append([a, res, 0])
	            elsif queryComp.include?("Top")==true && answerComp.include?("Top")==true

	              hashComp[c].append([a, 'equiv', 0])
	            elsif queryComp.include?("Top")==true
	            	hashComp[c].append([a, 'fm', 0])
	            else
	              hashComp[c].append([a, 'fr', 0])
	            end
	          else #answer doesn't have that component, meaning there we can directly put rest = component (L21 de l'algo vers L22)
	            hashComp[c].append([a, 'fr', 0])
	          end

	        end
	      else # query doesn't have that component, meaning there we can directly put miss = component (dernier sinon L47 de l'algo vers L60)

	        answerList.each_key do |a|
	          if answerList[a].include?(c)
	            hashComp[c].append([a, 'fm', 0])
	          else # query and answer both don't have the component, they are equivalent for that component
	            hashComp[c].append([a, 'equiv', 0])
	          end

	        end
	      end
	      @compSub.merge!(@compSub, hashComp)  
	    end

	@tempFonc.tempPrint("Comparaison des réponses avec la requête")

puts "Comparaison des réponses avec la requête"


	 CCO()
end







def comparaisonComposante(classiAFaire, query, answer, normB, classiF) # fonction qui ne sert que pour les tests qualitatif

     @funcBaad=normB
	    @funcClass=classiF

    classi=@funcClass.classiBaaderComp(classiAFaire, query, answer, normB)

    if (classi['Answer'].include?('Query') && classi['Query'].include?('Answer')) # la reponse et la requete sont équivalentes
      return 'equiv'
    elsif classi['Answer'].include?('Query') #la reponse est subsumée par la requête
      return 'subsumed'
    elsif  classi['Query'].include?('Answer')  #la reponse subsume la requête
      return 'subsuming'

    else #pas de relation
      return 'nr'
    end
    

end

def comparaisonComposanteMissRest(query, answer, normB, classiF) #comparaison des relations de subsomptions entre rest ou miss de deux reponses, on a gardé query/answer pour plus de simplicité

     @funcBaad=normB
	    @funcClass=classiF


    classi=@funcClass.classiBaaderMissRest(query, answer, normB)



    if (classi['Answer'].include?('Query') && classi['Query'].include?('Answer')) # la reponse et la requete sont équivalentes
      return 'equiv'
    elsif classi['Answer'].include?('Query') #la reponse est subsumée par la requête
      return 'subsuming'
    elsif  classi['Query'].include?('Answer')  #la reponse subsume la requête
      return 'subsumed'

    else #pas de relation
      return 'nr'
    end
    

end


def CCO()	
	 @tempFonc.tempPrintConsole("debut cco")

	@compSub.each_key do |comp|

		for i in 0..@compSub[comp].length-1
			puts "rep "+i.to_s
        	for j in i+1..@compSub[comp].length-1

        		@compteurCompa=@compteurCompa+1
        		if @compSub[comp][i][1]=='equiv'#donc i equiv à la requete
        			if @compSub[comp][j][1]=='equiv'
		                #"égalité"

		              else
		                #'i gagne'
		                @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                @compSub[comp][j][2]=@compSub[comp][j][2]-1
		              end
        		elsif @compSub[comp][i][1]=='subsumed'#donc i inclus dans la requete
        			if @compSub[comp][j][1]=='equiv'
		                #'j gagne'
		                @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                @compSub[comp][j][2]=@compSub[comp][j][2]+1
		            elsif @compSub[comp][j][1]=='subsumed'
		                #'comparaison du miss'
		                i1=@fupReponse[@compSub[comp][i][0]].index(comp)
		                a1=@fupReponse[@compSub[comp][i][0]][i1+1].map(&:clone)
		                
		                i2=@fupReponse[@compSub[comp][j][0]].index(comp)
		                a2=@fupReponse[@compSub[comp][j][0]][i2+1].map(&:clone)
		                
		                cIndex2=@fupDemande.index(comp)
		                qC= @fupDemande[cIndex2+1].map(&:clone)
		                @compteurDiff=@compteurDiff+1

		                @tempFonc.tempDiff()
		                result=compMiss(qC, a1, a2)
		                if result=="subsumed"
		               	result=-1
		               elsif result=="subsuming"
		               	result=+1
		                end

		                if result=="equiv" || result=="nr"
		                	result=compTaille(qC,a1,a2)
		                end
		                @tempFonc.tempDiffEnd()

		                if result==1
		                  #'i gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result==-1
		                  #j gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                elsif result=="d1"
		                	 @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result=="d2"
		                 @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                end
		                  
		            else
		                #'i gagne'
		                @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                @compSub[comp][j][2]=@compSub[comp][j][2]-1
		            end

        		elsif @compSub[comp][i][1]=='subsuming' || @compSub[comp][i][1]=='nr'   #donc i subsume la requete ou pas de relation
        			if @compSub[comp][j][1]=='equiv' || @compSub[comp][j][1]=='subsumed'
		                #'j gagne'
		                @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                @compSub[comp][j][2]=@compSub[comp][j][2]+1
		            elsif @compSub[comp][j][1]=='subsuming'
		            	#comp rest
		            	i1=@fupReponse[@compSub[comp][i][0]].index(comp)
		                a1=@fupReponse[@compSub[comp][i][0]][i1+1].map(&:clone)
		                
		                i2=@fupReponse[@compSub[comp][j][0]].index(comp)
		                a2=@fupReponse[@compSub[comp][j][0]][i2+1].map(&:clone)
		                
		                cIndex2=@fupDemande.index(comp)
		                qC= @fupDemande[cIndex2+1].map(&:clone)
		                @compteurDiff=@compteurDiff+1

		                @tempFonc.tempDiff()
		                result=compRest(qC, a1, a2)
		                if result=="equiv" || result=="nr"
		                	result=compMiss(qC, a1, a2)
		                end

		                if result=="subsumed"
		               	result=-1
		               elsif result=="subsuming"
		               	result=1
		                end

		                if result=="equiv" || result=="nr"
		                	result=compTaille(qC,a1,a2)
		                end
		                @tempFonc.tempDiffEnd()

		                if result==1
		                  #'i gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result==-1
		                  #j gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                elsif result=="d1"
		                	 @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result=="d2"
		                 @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                end
		            elsif  @compSub[comp][j][1]=='fr'
		            #'i gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1    
		            else
		            	#comp both
		            	i1=@fupReponse[@compSub[comp][i][0]].index(comp)
		                a1=@fupReponse[@compSub[comp][i][0]][i1+1].map(&:clone)
		                
		                i2=@fupReponse[@compSub[comp][j][0]].index(comp)
		                a2=@fupReponse[@compSub[comp][j][0]][i2+1].map(&:clone)
		                
		                cIndex2=@fupDemande.index(comp)
		                qC= @fupDemande[cIndex2+1].map(&:clone)
		                @compteurDiff=@compteurDiff+1

		                @tempFonc.tempDiff()
		                result=compRest(qC, a1, a2)

		                if result=="equiv" || result=="nr"
		                	result=compMiss(qC, a1, a2)
		                end

		                if result=="subsumed"
		               	result=-1
		                elsif result=="subsuming"
		               	result=1
		                end

		                if result=="equiv" || result=="nr"
		                	result=compTaille(qC,a1,a2)
		                end
		                @tempFonc.tempDiffEnd()


		               
		                if result==1
		                  #'i gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result==-1
		                  #j gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                elsif result=="d1"
		                	 @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result=="d2"
		                 @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                end
		                
		            end

        		elsif @compSub[comp][i][1]=='fr'
        			if @compSub[comp][j][1]=='fr' # => les deux reponses sont juste ["Top"]
                		result=0
                	else
                		result==-1
                	end

        		elsif @compSub[comp][i][1]=='fm'
        			if @compSub[comp][j][1]=='fm' 
                		# 'comparaison du miss'
		                i1=@fupReponse[@compSub[comp][i][0]].index(comp)
		                a1=@fupReponse[@compSub[comp][i][0]][i1+1].map(&:clone)
		                
		                i2=@fupReponse[@compSub[comp][j][0]].index(comp)
		                a2=@fupReponse[@compSub[comp][j][0]][i2+1].map(&:clone)
		                
		                cIndex2=@fupDemande.index(comp)
		                qC= @fupDemande[cIndex2+1].map(&:clone)
		                @compteurDiff=@compteurDiff+1

		                @tempFonc.tempDiff()
		                result=compMiss(qC, a1, a2)
		                
		                if result=="equiv" || result=="nr"
		                	result=compTaille(qC,a1,a2)
		                end
		                @tempFonc.tempDiffEnd()

		                if result=="subsumed"
		               	result=-1
		                elsif result=="subsuming"
		               	result=1
		                end
		                if result==1
		                  #'i gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result==-1
		                  #j gagne'
		                  @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                elsif result=="d1"
		                	 @compSub[comp][i][2]=@compSub[comp][i][2]+1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]-1
		                elsif result=="d2"
		                 @compSub[comp][i][2]=@compSub[comp][i][2]-1
		                  @compSub[comp][j][2]=@compSub[comp][j][2]+1
		                end
                	elsif @compSub[comp][j][1]=='fr' # => normalement inutile
                		result==1
                	else
                		result==-1
                	end
        		else
        			
        		end	

        	end
        end
    end

      @tempFonc.tempPrintConsole("fin cco")
    @tempFonc.tempPrint("Fin des comparaisons")

    @compSub.each_key do |comp|
      @compSub[comp]=@compSub[comp].sort_by(&:last).reverse
    end
    puts "Score de composantes"
    puts @compSub.inspect

    classement1={}
    @answerList.each_key do |a|
      classementTemp={a=>0}
       classement1.merge!(classementTemp)
    end

     @compSub.each_key do |comp|

      for i in 0..@compSub[comp].length-1
        classementTemp={@compSub[comp][i][0] => @compSub[comp][i][2]+classement1[@compSub[comp][i][0]]}
        classement1.merge!(classementTemp)
      end
      
    end

     classement1= classement1.sort_by(&:last).reverse
     @tempFonc.tempPrint("Fin du classement")
     @tempFonc.tempTotal("Total du traiement")
     puts 
     puts "Classement des documents"
     puts classement1.inspect
     puts
     puts "++++++++++++"
     return classement1
     
end

def compRest(query, answer1, answer2)

	queryCompC=query.map(&:clone)
	answerCompC1=answer1.map(&:clone)
	r1=@tso.tso(queryCompC, answerCompC1)
	queryCompC=query.map(&:clone)
	answerCompC2=answer2.map(&:clone)
	r2=@tso.tso(queryCompC, answerCompC2)

	if r1!='Top' && r1!='&'
      a1=r1.map(&:clone)
	  	  else
	  a1=["Top"]
	  end
	  if r2!='Top' && r2!='&'
      a2=r2.map(&:clone)
	  	  else
	  a2=["Top"]
	  end


		if a1==["Top"] && a2==["Top"]
		result="equiv"
	elsif a1==["Top"]
		result="subsuming"
	elsif a2==["Top"]
		result="subsumed"
	else

    hashClone=Marshal.load(Marshal.dump(@classi))	
	result=comparaisonComposanteMissRest(a1, a2, @funcBaad, @funcClass)

end
    return result

end


def compMiss(query, answer1, answer2)


	queryCompC=query.map(&:clone)
	answerCompC1=answer1.map(&:clone)
	r1=@tso.tso(answerCompC1, queryCompC)
	queryCompC=query.map(&:clone)
	answerCompC2=answer2.map(&:clone)
	r2=@tso.tso(answerCompC2, queryCompC)

	  	if r1!='Top' && r1!='&'
      a1=r1.map(&:clone)
	  	  else
	  a1=["Top"]
	  end
	  if r2!='Top' && r2!='&'
      a2=r2.map(&:clone)
	  else
	  a2=["Top"]
	  end


	if a1==["Top"] && a2==["Top"]
		result="equiv"
	elsif a1==["Top"]
		result="subsuming"
	elsif a2==["Top"]
		result="subsumed"
	else
		

 	hashClone=Marshal.load(Marshal.dump(@classi))
	result=comparaisonComposanteMissRest(a1, a2, @funcBaad, @funcClass)

 	end

    return result
  end

   #comparaison de la taille des rest ou miss
  def compTaille(query, answer1, answer2) 
  	l1=0
  	l2=0

  	queryCompC=query.map(&:clone)
	answerCompC1=answer1.map(&:clone)
	r1=@tso.tso(queryCompC, answerCompC1)
	queryCompC=query.map(&:clone)
	answerCompC2=answer2.map(&:clone)
	r2=@tso.tso(queryCompC, answerCompC2)

	queryCompC=query.map(&:clone)
	answerCompC1=answer1.map(&:clone)
	m1=@tso.tso(answerCompC1, queryCompC)
	queryCompC=query.map(&:clone)
	answerCompC2=answer2.map(&:clone)
	m2=@tso.tso(answerCompC2, queryCompC)


	r1=r1.flatten
	r2=r2.flatten
  	
  	if r1.length<r2.length
  		return "d1"
  	elsif r1.length>r2.length
  		return "d2"
  	else
  	m1=m1.flatten
	m2=m2.flatten
	if m1.length<m2.length
		return "d1"
  	elsif m1.length>m2.length
  		return "d2"
  	else
  		return "equiv"
  	end
	end


  end


end


class Tempo
  	def initialize(fichier)
    	@start =Time.now.to_f
    	@timeNow=0
    	@timeDiffIni=0
    	@timeDiffEnd=0
    	@tempDiffTotal=0
    	@fichier=fichier
    	@fileR = File.open(fichier, 'w'){ |f| f.write "#{@start} - Test Started\n" }
  	end

  	def setFichier(fichier)
  		@fichier=fichier
  		@start =Time.now.to_f
  	end

  	def tempPrint(intitulé)
  		@timeNow=Time.now.to_f-@start
		File.write(@fichier, "#{intitulé}: #{@timeNow}\n", mode: "a")
 	end

 	def tempPrintConsole(intitulé)
  		@timeNow=Time.now.to_f-@start
		puts "#{intitulé}: #{@timeNow}\n"
 	end

 	def tempTotal(intitulé)
  		@timeNow=Time.now.to_f-@start
		puts "#{intitulé}: #{@timeNow}\n"
 	end

    def tempF()
  		@timeNow=Time.now.to_f-@start
	 	File.write(@fichier, "Temps Total: #{@timeNow}\n", mode: "a")
  	end

  	def tempDiff() 
  		@timeDiffIni=Time.now.to_f-@start


  	end

  	def tempDiffEnd()
  		@timeDiffEnd=Time.now.to_f-@start
  		timeDiff=@timeDiffEnd-@timeDiffIni
  		@tempDiffTotal=@tempDiffTotal+timeDiff

  	end

  	def tempDiffTotal()
  		File.write(@fichier, "Temps passé à calculer des différences: #{@tempDiffTotal}\n", mode: "a")
  	end

  	  def NumberPrint(intitulé, number)
		File.write(@fichier, "#{intitulé}: #{number}\n", mode: "a")
 	end

 	def resultPrint(tab)
 		File.write(@fichier, "#{tab}}\n", mode: "a")
 	end

 	def fclose()
 		#@fileR.close
 	end
end



class Testing

	def lancementCCO(onto, demande, descriTab, compoTab)

		vTemp=Tempo.new("void")
		
		normB=Normalisation.new
		classi=Classification.new
		fup=FillUP.new
		cco=CCO.new(vTemp, compoTab)
		prop=Hash.new("void")

		puts "__________________________________________________________________________________________________________________"

		#########################################################################################################

		for i in 0..descriTab.length-1 do
			prop[""+i.to_s] = descriTab[i]
		end
		puts "reponses mises en hash"
		####################################    NORMALISATION   #####################################################

		ontoF=onto.map(&:clone)
		result=normB.preNorm(ontoF)
		vTemp.tempPrint("Normalisation")
		puts "norma done"
		#########################################   CLASSIFICATION   ##################################################
		ontoF=result.map(&:clone)
	
		hashC=classi.ontoHash(result)
		result=classi.classiBaader(ontoF, hashC)
	
		hashC=result


		classi.setClassiIni(hashC)
		classi.setOntoIni(ontoF)
		puts "classi done"
		
		#######################################     FUP REPONSE    ################################################

		propFup=Marshal.load(Marshal.dump(prop))
		for i in 0..propFup.length-1 do
			enCours=propFup[i.to_s]
			for j in 0..compoTab.length-1 do
				fup.setNamePrefix(i.to_s)
				fup.setCompoSuffix(compoTab[j])
				testsTemp=fup.preFup(ontoF, hashC, enCours[j*3+1], normB, classi)
				hashC=fup.returnClassi()
				enCours[1+j*3]=testsTemp
			end
		end

		puts "Fup des reponses done"

		# on a : Onto norma et classifiée, reponse fup, demande fup
		#########################################################################################################


		###############################    FUP DEMANDE    ############################################
		demandeFup= demande.map(&:clone)
		for i in 0..compoTab.length-1 do
		fup.setNamePrefix("Q")
		fup.setCompoSuffix(compoTab[i])
		testsTemp=[]
		testsTemp=fup.preFup(ontoF, hashC, demandeFup[i*3+1], normB, classi)
		hashC=fup.returnClassi()
		demandeFup[1+i*3]=testsTemp
		end

		

		puts "Fup de la demande done"
		
		ontoClone=ontoF.map(&:clone)

		cco.setFupDemande(demandeFup)

		cco.setFupReponse(propFup)
		fup.setNamePrefix("F")




		classement=cco.componentComparison(ontoClone, hashC, demande, prop, normB, classi, fup)


		File.write("ResultQualitatif/CCO.txt", "Ontologie : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", onto.to_s, mode: "a")
  		File.write("ResultQualitatif/CCO.txt", "\nDemande : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", demande.to_s, mode: "a")
  		File.write("ResultQualitatif/CCO.txt", "\nRéponses : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", prop.to_s, mode: "a")
  		File.write("ResultQualitatif/CCO.txt", "\nRéponsesFup : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", propFup.to_s, mode: "a")
  		File.write("ResultQualitatif/CCO.txt", "\nClassi : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", hashC.to_s, mode: "a")
  		File.write("ResultQualitatif/CCO.txt", "\nClassement finale : ", mode: "a")
  		File.write("ResultQualitatif/CCO.txt", classement.to_s, mode: "a")
		File.write("ResultQualitatif/CCO.txt", "\n\n", mode: "a")


		########################################################################################################



	end

	
end
if __FILE__ == $0


require 'json'


#Normalisation Baader
  File.write("ResultQualitatif/Baader.txt", "Normalisation Baader\n", mode: "w")
  nB=Normalisation.new
  onto=[['A', '=', 'B']] # Normalisation des equivalences
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['A', 'subs', 'B']] # ne fais rien
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['A', 'subs', 'B', '&', 'C']] # NF5
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['A', '&', 'B', '&', 'C', 'subs', 'D']] # NF1
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['A', '&', '*R.', ['B'], 'subs', 'C']] # NF1 avec un rôle
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['A', '&', '*R.', ['B'], '&', 'D', 'subs', 'C']] # NF1 avec un rôle
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['*R.', ['B'], '&', 'D', 'subs', 'C']] # NF1 avec un rôle
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['*R.', ['B', '&', 'D'], 'subs', 'C']] # NF2 avec une conjonction
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  onto=[['*R.', ['*S.', ['D']], 'subs', 'C']] # NF2 avec un role
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")


  nB=Normalisation.new
  onto=[['C', 'subs','A', '&', '*R.', ['B']]] #NF5 avec un role
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['C', 'subs','A', '&', '*R.', ['B'], '&', 'D']] #NF5 avec un role
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['C', 'subs','*R.', ['B'], '&', 'D']] #NF5 avec un role
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")
  nB=Normalisation.new
  onto=[['C', 'subs','*R.', ['B', '&', 'D']]] # NF4 avec une conjonction
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  onto=[['C', 'subs','*R.', ['*S.', ['D']]]] # NF4 avec un role
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")

    nB=Normalisation.new
  onto=[['C', '&', '*R.', ['A', '&', 'B'], 'subs','*R.', ['*S.', ['D'], "&", "E"], '&', 'F']] # conjonction des deux côtés avec des rôles complexes
  ontoF=onto.map(&:clone)
  result=nB.preNorm(onto)

  File.write("ResultQualitatif/Baader.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Baader.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Baader.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Baader.txt", "\n\n", mode: "a")


#-----------------------------------------------------------------------------------------------------------------------------------------------
#classification
  fileR = File.open("ResultQualitatif/Classi.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }
  nB=Normalisation.new

  classi=Classification.new
  onto=[['A', 'subs', 'B']] # CR1
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', '=', 'B']] # CR1
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', 'C']] # CR1 
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*X.',['Y']]] # CR3
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['*X.',['Y'], 'subs', 'A']] 
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")


  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', '&', 'A', 'subs', 'C'] ] # CR2
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)
    File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")


  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*R.', ['D']], ['*R.', ['D'], 'subs', 'E'] ] #CR4
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")


  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', '&', 'A', 'subs', '*R.', ['D']], ['*R.', ['D'], 'subs', 'E'] ] #CR1 + CR2 + #CR4
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

    nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', '&', 'A', 'subs', '*R.', ['D']], ['*R.', ['D'], 'subs', 'E'], ['E', 'subs', 'F', '&', 'G'] ] #CR1 + CR2 + CR3 + #CR4 + CR1 again
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

      nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', '&', 'A', 'subs', '*R.', ['D']], ['*R.', ['D'], 'subs', 'E'], ['E', 'subs', 'F', '&', 'G'], ['B', '&', 'G', 'subs','H'] ] #CR1 + CR2 + #CR4 + CR1 again + CR2 again
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['*X.',['Y' ,'&', 'Z'], '=', 'A'], ['*X.',['Y'] ,'&', '*X.',['Z'], '=', 'B']] 
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  File.write("ResultQualitatif/Classi.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Classi.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\nResult :\n", mode: "a")
  File.write("ResultQualitatif/Classi.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Classi.txt", "\n\n", mode: "a")

  #-----------------------------------------------------------------------------------------------------------------------------------------------
#Fill-up
  fileR = File.open("ResultQualitatif/Fup.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['A']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

    nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['B']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['Top']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['*R.', ['A']]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")


  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['C', 'subs', 'D']]
  req=['A', '&', 'C']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, hashC, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['C', 'subs', 'D']]
  req=['*R.', ['A'], '&', 'C']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['C', 'subs', 'D']]
  req=['*R.', ['*S.', ['A']], '&', 'C']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

    nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*R.', ['B']], ['C', 'subs', '*R.', ['D']], ['D', 'subs', 'E'], ['E', 'subs', '*S.', ['F']]]
  req=['A', '&', 'C']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

   fileR = File.open("ResultQualitatif/Fup.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }  

       nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*R.', ['B']], ['C', 'subs', '*R.', ['D']], ['D', 'subs', 'E'], ['E', 'subs', '*S.', ['F']]]
  req=['A', '&', '*r.', ["Top"], "&", "*s.", ["Top", "&", "H"]]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
  ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)

  classiD=classi.classiBaader(ontoNorm, hashC)
  fup=FillUP.new
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
  result=fup.preFup(ontoNorm, classiD, reqD, nB, classi)
  classiF=fup.returnClassi()

  File.write("ResultQualitatif/Fup.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nOntologie normalisée: ", mode: "a")
  File.write("ResultQualitatif/Fup.txt", ontoN.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi au début :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nClassi à la fin :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", classiF.to_s, mode: "a")
    File.write("ResultQualitatif/Fup.txt", "\nDescription originelle:\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nDescription :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", reqD.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\nResultat du Fup :\n", mode: "a")
  File.write("ResultQualitatif/Fup.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/Fup.txt", "\n\n", mode: "a")

#-----------------------------------------------------------------------------------------------------------------------------------------------
#TSO



  fileR = File.open("ResultQualitatif/tso.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }  
  cso=TSO.new

  d=['A']
  d2=['A']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A']
  d2=['B']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['Top']
  d2=['Top']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A']
  d2=['Top']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A', '&', 'B']
  d2=['A']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A', '&', 'B']
  d2=['A', '&', 'B']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A', '&', 'B']
  d2=['A', '&', 'B', '&', 'C']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['A', '&', 'B', '&', 'C']
  d2=['A', '&', 'B']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")


  d=['*R.', ['A']]
  d2=['A']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A']]
  d2=['*R.', ['A']]
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A', '&', 'B']]
  d2=['*R.', ['A']]
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A', '&', 'B'], '&', 'C', '&', 'D']
  d2=['*R.', ['A'], '&', 'C', '&', 'E']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A', '&', 'B'], '&', 'C', '&', 'D']
  d2=['*S.', ['A'], '&', 'C', '&', 'E']
  d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A', '&', 'B', '&', '*S', ['A']], '&', 'C', '&', 'D']


  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

  d=['*R.', ['A', '&', 'B', '&', '*S', ['A']], '&', 'C', '&', 'D']
  d2=['*R.', ['A', '&', '*S', ['A']], '&', 'C', '&', 'E']
  d1=['*R.', ['A', '&', 'B', '&', '*S', ['A']], '&', 'C', '&', 'D']
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")


   d=['*R.', ['A']]
  d1=d.map(&:clone)
    d2=['*R.', ['Top']]
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")

     d2=['*R.', ['A']]

    d=['*R.', ['Top']]
      d1=d.map(&:clone)
  result=cso.tso(d1, d2)

  File.write("ResultQualitatif/tso.txt", "Descriptions : ", mode: "a")
  File.write("ResultQualitatif/tso.txt", d.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", d2.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\nResultat du TSO :\n", mode: "a")
  File.write("ResultQualitatif/tso.txt", result.to_s, mode: "a")
  File.write("ResultQualitatif/tso.txt", "\n\n", mode: "a")



  #-----------------------------------------------------------------------------------------------------------------------------------------------
#Calcul de subsomption
	fichierTemps="void.txt"
	vTemp=Tempo.new(fichierTemps)
	compoTab=["*A."]
  fileR = File.open("ResultQualitatif/subsomption.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }  
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['*A.', ['A']]
  ans=['*A.', ['A']]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")


  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['*A.', ['A']]
  ans=['*A.', ['B']]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")


  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['*A.', ['A']]
  ans=['*A.', ['C']]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")


  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*r.', ['B']]]
  req=['*A.', ['A']]
  ans=['*A.', ['*r.', ['B']]]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")


  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*r.', ['B']]]
  req=['*A.', ['A']]
  ans=['*A.', ['*r.', ['C']]]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")


  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', '*r.', ['B']]]
  req=['*A.', ['*r.', ['B', '&', 'C']]]
  ans=['*A.', ['*r.', ['B'], '&', '*r.', ['C']]]
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)



  		rep=cco.comparaisonComposante(result, req, ans,nB, classi)
		hashClone=Marshal.load(Marshal.dump(hashC))
		ontoClone=ontoF.map(&:clone)

  File.write("ResultQualitatif/subsomption.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\nResultat subsomption :\n", mode: "a")
  File.write("ResultQualitatif/subsomption.txt", rep.to_s, mode: "a")
  File.write("ResultQualitatif/subsomption.txt", "\n\n", mode: "a")




  #-----------------------------------------------------------------------------------------------------------------------------------------------
#Rest et Miss

	fichierTemps="void.txt"
	vTemp=Tempo.new(fichierTemps)
	
  fileR = File.open("ResultQualitatif/RestMiss.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" }  
  compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  fup=FillUP.new
  onto=[['A', 'subs', 'B']]
  req=['A']
  ans=['B']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
    hashClone=fup.returnClassi()

      fup.setNamePrefix("B")
  fup.setCompoSuffix("1")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")


    compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B']]
  req=['A']
  ans=['A']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
    hashClone=fup.returnClassi()
      fup.setNamePrefix("A")
  fup.setCompoSuffix("2")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

      compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', 'C']]
  req=['C']
  ans=['A']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("C")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
   hashClone=fup.returnClassi()
      fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

        compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']]]
  req=['*r.', ['C']]
  ans=['A']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("C")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
    fup.setNamePrefix("A")
  fup.setCompoSuffix("1")

    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

          compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']]]
  req=['*r.', ['C'], '&', 'D']
  ans=['A']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("D")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

            compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']]]
  req=['*r.', ['C'], '&', 'D']
  ans=['A', '&', 'E']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("D")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

      compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']], ['A', '&', 'E', 'subs', 'D']]
  req=['*r.', ['C'], '&', 'D']
  ans=['A', '&', 'E']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("D")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("A")
  fup.setCompoSuffix("1")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

        compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']], ['A', '&', 'E', 'subs', 'D']]
  req=['*r.', ['C'], '&', 'D']
  ans=['X']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("D")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
	      fup.setNamePrefix("X")
  fup.setCompoSuffix("X")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

          compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']], ['A', '&', 'E', 'subs', 'D'], ['X', "=", 'Y']]
  req=['*r.', ['C'], '&', 'Y']
  ans=['X']
  reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("Y")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("X")
  fup.setCompoSuffix("X")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")


          compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']], ['A', '&', 'E', 'subs', 'D'], ['X', "=", 'Y'], ['*r.', ['X'], 'subs', 'Z']]
  req=['*r.', ['C'], '&', 'Y']
  ans=['*r.', ['Y']]
    reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("Y")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("X")
  fup.setCompoSuffix("X")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

            compoTab=["*A."]
  cco=CCO.new(vTemp, compoTab)
  nB=Normalisation.new
  classi=Classification.new
  onto=[['A', 'subs', 'B'], ['B', 'subs', '*r.', ['C']], ['A', '&', 'E', 'subs', 'D'], ['X', "=", 'Y'], ['*r.', ['X'], 'subs', 'Z']]
  req=['*r.', ['C'], '&', 'Y']
  ans=['*r.', ['Y', '&', 'X']]
    reqD=req.map(&:clone)
  ontoF=onto.map(&:clone)
    ontoNorm=nB.preNorm(onto)
  ontoN=ontoNorm.map(&:clone)
  hashC=classi.ontoHash(ontoNorm)
  result=classi.classiBaader(ontoNorm, hashC)

  ontoN=ontoNorm.map(&:clone)
  hashClone=Marshal.load(Marshal.dump(result))
  fup.setNamePrefix("Y")
  fup.setCompoSuffix("1")
    fupReq=fup.preFup(ontoN, hashClone, req, nB, classi)
	hashClone=fup.returnClassi()
      fup.setNamePrefix("X")
  fup.setCompoSuffix("X")
    fupAns=fup.preFup(ontoN, hashClone, ans, nB, classi)

  cso=TSO.new

  d1=fupReq.map(&:clone)
  d2=fupAns.map(&:clone)
  rest=cso.tso(d1, d2)
  miss=cso.tso(d2, d1)

  File.write("ResultQualitatif/RestMiss.txt", "Ontologie : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ontoF.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nDescriptions : ", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Requete:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", req.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n Reponse:", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", ans.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\nRest :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", rest.to_s, mode: "a")
    File.write("ResultQualitatif/RestMiss.txt", "\nMiss :\n", mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", miss.to_s, mode: "a")
  File.write("ResultQualitatif/RestMiss.txt", "\n\n", mode: "a")

  #-----------------------------------------------------------------------------------------------------------------------------------------------
#CCO
	fichierTemps="void.txt"
	vTemp=Tempo.new(fichierTemps)



  fileR = File.open("ResultQualitatif/CCO.txt", 'w'){ |f| f.write "#{Time.now} - Test Started\n" } 
	onto=[['A', 'subs', 'B']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['A']], ['*A.',['B']]]
	testCCO=Testing.new
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)





  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['A']], ['*A.',['C']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['A']], ['*A.',['C']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A'], ['B', 'subs', 'D']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['A']], ['*A.',['D']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A'], ['B', 'subs', 'D']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['E']], ['*A.',['D']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A'], ['B', 'subs', 'D']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['E', '&', 'A']], ['*A.',['D']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['B', 'subs', 'A'], ['C', 'subs', 'A'], ['D', 'subs', 'B'], ['E', 'subs', 'A']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['C']], ['*A.',['D']], ['*A.',['A']], ['*A.',['E']], ['*A.',['D', '&', 'X']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

 
  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A'], ['B', 'subs', 'D']]
	demande= ['*A.',['B']]
	descriTab =[['*A.',['A']], ['*A.',['A', '&', 'X']], ['*A.',['X']], ['*A.',['B']], ['*A.',['D', '&', 'X']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)


  		normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A', 'subs', 'B'], ['C', 'subs', 'A'], ['B', 'subs', 'D'], ['Z', 'subs', '*r.', ['X']]]
	demande= ['*A.', ['B', '&', '*r.', ['X', '&', 'Y']]]
	descriTab =[ ['*A.',['A']], ['*A.',['A', '&', 'X']], ['*A.',['*r.', ['X'], '&', 'Y']], ['*A.',['Z']], ['*A.',['D', '&', '*s.', ['X'] ]] ]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)


  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A.", "*B."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*A.',['A1'], '&', '*B.', ['B1']]
	descriTab =[['*A.', ['A2'], '&', '*B.', ['B2']], ['*A.',['A1'], '&', '*B.', ['B1']], ['*A.',['A1'], '&', '*B.', ['B2']], ['*A.',['A2'], '&', '*B.', ['B1']], ['*A.',['A2', '&', 'A1'], '&', '*B.', ['B1']], ['*A.',['A3'], '&', '*B.', ['B1']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

	  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*A.',['A1']]
	descriTab =[['*A.', ['A2']], ['*A.',['A1']], ['*A.',['A1']], ['*A.',['A2']], ['*A.',['A2', '&', 'A1']], ['*A.',['A3']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

	  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*B."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*B.', ['B1']]
	descriTab =[['*B.', ['B2']], ['*B.', ['B1']], ['*B.', ['B2']], ['*B.', ['B1']], ['*B.', ['B1']], ['*B.', ['B1']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

	  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A.", "*B.", "*C."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*A.',['A1'], '&', '*B.', ['B1'], "&", '*C.', ['top']]
	descriTab =[['*A.',['A1'], '&', '*B.', ['B1'], "&", '*C.', ['C2']], ['*A.',['A1'], '&', '*B.', ['B1'], "&", '*C.', ['top']], ['*A.',['A2'], '&', '*B.', ['B2'], "&", '*C.', ['top']] , ['*A.',['A1'], '&', '*B.', ['B2'], "&", '*C.', ['top']], ['*A.',['A2'], '&', '*B.', ['B1'], "&", '*C.', ['top']] , ['*A.',['A2', '&', 'A1'], '&', '*B.', ['B1'], "&", '*C.', ['top']], ['*A.',['A3'], '&', '*B.', ['B1'], "&", '*C.', ['top']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

		  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*A."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*A.',['A1']]
	descriTab =[['*A.',['A1']], ['*A.',['A1']], ['*A.',['A2']] , ['*A.',['A1']], ['*A.',['A2']] , ['*A.',['A2', '&', 'A1']], ['*A.',['A3']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

		  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*B."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*B.', ['B1']]
	descriTab =[['*B.', ['B1']], ['*B.', ['B1']], ['*B.', ['B2']] , ['*B.', ['B2']], ['*B.', ['B1']] , ['*B.', ['B1']], ['*B.', ['B1']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)

		  	normB=Normalisation.new
	classi=Classification.new
	compoTab=["*C."]
	fuP=FillUP.new
	cco=CCO.new(vTemp, compoTab)	
	prop=Hash.new("void")	
	onto=[['A2', 'subs', 'A1'], ['B2', 'subs', 'B1']]
	demande= ['*C.', ['top']]
	descriTab =[['*C.', ['C2']], ['*C.', ['top']], ['*C.', ['top']] , ['*C.', ['top']], ['*C.', ['top']] , ['*C.', ['top']], ['*C.', ['top']]]
	testCCO.lancementCCO(onto, demande, descriTab, compoTab)



end