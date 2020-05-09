#include "automate.h"


AUTOMATE automate_creer (int Q){
	AUTOMATE A;
	A.sigma = 26;
	A.Q = Q;
	A.F = calloc(Q,sizeof(int)); //calloc place des zéros dans le tableau: aucun état final
	A.T = calloc(Q,sizeof(TRANSITION));//les 0 placés par calloc correspondent à NULL: toutes les listes sont vides, pas de transition
	return A;
} 

void automate_ajouter_transition (AUTOMATE A, int dep, char car, int arr){
	TRANSITION T = A.T[dep];
	while(T){ //teste si la transition existe et ne fait rien si c'est le cas
		if(T->car == car && T->arr == arr) return;
		T = T->suiv;
	}
	TRANSITION new = malloc(sizeof(struct transition));
	new->car = car;
	new->arr = arr;
	new->suiv = A.T[dep];
	A.T[dep] = new;
}

/*TRANSITION supprimer_transition(TRANSITION T, char car, int arr){
	if(!T) return NULL;
	if(T->car == car && T->arr == arr) {
		TRANSITION suivant = T->suiv;
		free(T);
		return suivant;
	}
	T->suiv = supprimer_transition(T->suiv,car,arr);
	return T;
}*/

/*void automate_supprimer_transition (AUTOMATE A, int dep, char car, int arr){
	supprimer_transition(A.T[dep],car,arr);
}*/

void automate_ajouter_final (AUTOMATE A, int q){
	A.F[q] = 1;
}

void automate_supprimer_final (AUTOMATE A, int q){
	A.F[q] = 0;
}


TRANSITION copie_liste(TRANSITION T, int decalage, int conserve_epsilon){
	if(!T) return NULL;
	if(!conserve_epsilon && T->car == -1) return copie_liste(T->suiv,decalage,conserve_epsilon);
	TRANSITION nouveau = malloc(sizeof(struct transition));
	nouveau->car = T->car;
	nouveau->arr = T->arr + decalage;	
	nouveau->suiv = copie_liste(T->suiv,decalage,conserve_epsilon);
	return nouveau;
}

AUTOMATE automate_copier(AUTOMATE A, int conserve_epsilon){
	AUTOMATE B = automate_creer(A.Q);
	B.Q = A.Q;
	B.sigma = A.sigma;
	memcpy(B.F,A.F,A.Q*sizeof(int));
	for(int i = 0; i < A.Q; i++) B.T[i] = copie_liste(A.T[i],0,conserve_epsilon);
	return B;
}

void liberer_transition(TRANSITION T){
	if(T){
		liberer_transition(T->suiv);
		free(T);
	}
}

void automate_liberer_memoire(AUTOMATE A){
	free(A.F);
	for(int i = 0; i < A.Q; i++){
		liberer_transition(A.T[i]);
	}
	free(A.T);
}


void automate_ecrire (AUTOMATE A, char* nomfic){
	FILE *F = fopen(nomfic,"w");
	if(F == NULL){
    	printf("échec ouverture fichier %s\n", nomfic);
    	exit(0);
  	}
  	int nombre_finaux = 0;
  	for(int i = 0; i < A.Q; i++) nombre_finaux += A.F[i];
  	int nombre_transition = 0;
  	for(int i = 0; i < A.Q; i++){
  		TRANSITION l = A.T[i];
  		while(l){
  			nombre_transition++;
  			l = l-> suiv;
  		}
  	}
  	fprintf(F,"%d %d %d\n",A.Q,nombre_finaux,nombre_transition);
  	for(int i = 0; i < A.Q; i++){
  		if(A.F[i]) fprintf(F,"%2d ",i);
  	}
  	fprintf(F,"\n");
  	for(int i = 0; i < A.Q; i++){
  		TRANSITION l = A.T[i];
  		while(l){
  			fprintf(F,"%2d %c %2d\n",i,l->car,l->arr);
  			l = l-> suiv;
  		}
  	}
  	fclose(F);
}
/*
Q F T
F_1 F_2 F_3 ... F_F
dep_1 car_1 arr_1
dep_2 car_2 arr_2
...
dep_T car_T arr_T
Q : nombre d'états
F : nombre d'états finaux
T : nombres de transitions
F_i : les numéros des états finaux
dep_j car_j arr_J : une transition
*/
AUTOMATE automate_lire (char* nomfic){
	FILE *F = fopen(nomfic,"r");
	if(F == NULL){
    	printf("échec ouverture fichier %s\n", nomfic);
    	exit(1);
  	}
  	int nombre_etat, nombre_finaux, nombre_transition;
  	if( fscanf(F,"%d%d%d\n",&nombre_etat,&nombre_finaux,&nombre_transition) != 3) {
  		printf("Entete de fichier mal formé\n");
  		exit(2);
  	}
  	AUTOMATE A = automate_creer(nombre_etat);
  	for(int i = 0; i < nombre_finaux; i++){
  		int etat_final;
  		if(fscanf(F,"%d",&etat_final) != 1){
  			printf("État finaux mal formés\n");
  			exit(2);
  		}
  		automate_ajouter_final(A,etat_final);	
  	} 
  	for(int i = 0; i < nombre_transition; i++){
  		int dep, arr;
  		char car;
  		if(fscanf(F,"%d %c %d\n",&dep,&car,&arr) != 3){
  			printf("Transitions mal formées\n");
  			exit(2);	
  		}
  		automate_ajouter_transition(A,dep,car,arr);
  	}
  	fclose(F);
  	return A;
}


void parcours(AUTOMATE A, int etat, int* accessible){//parcours en profondeur du graphe des epsilons transitions
	//calcul accessible l'ensemble des états accessibles à partir de etat
	TRANSITION T = A.T[etat];
	while(T){
		if(T->car == -1 && !accessible[T->arr]){
			accessible[T->arr] = 1;
			parcours(A, T->arr, accessible);
		}
		T = T->suiv;
	}
}

int ** matrice_accessibilite(AUTOMATE A){//calcul la matrice d'accessibilité entre les sommets en utilisant uniquement
//les epsilon transitions
	int ** matrice = malloc(sizeof(int*)*A.Q);
	for(int i = 0; i < A.Q; i++) {
		matrice[i] = calloc(A.Q,sizeof(int));
		parcours(A,i,matrice[i]);
	}
	return matrice;
}


AUTOMATE automate_supprimer_epsilon(AUTOMATE A){

	AUTOMATE B = automate_copier(A,0);//recopie A en enlevant les epsilon transitions
	int **matrice = matrice_accessibilite(A);
	for(int i = 0; i < A.Q; i++){//fermeture avant à partir de A
		for(int j = 0; j < A.Q; j++){
			if(matrice[i][j]){
				if(A.F[j]) automate_ajouter_final(B,i);//on accède de i à un état final par un epsilon chemin donc i final
				TRANSITION T = B.T[j];
				while(T){//on parcourt toutes les transitions (j,c,j') pour ajouter la transition (i,c,j')
					automate_ajouter_transition(B,i,T->car,T->arr);
					T = T->suiv;
				}
			}
		}
	}
	for(int i=0; i< A.Q; i++) free(matrice[i]);
	free(matrice);
	return B;
}

AUTOMATE automate_epsilon(){
	AUTOMATE A = automate_creer(1);
	automate_ajouter_final(A,0);
	return A;
}

AUTOMATE automate_une_lettre(char car){
	AUTOMATE A = automate_creer(2);
	automate_ajouter_transition (A, 0, car, 1);
	automate_ajouter_final(A,1);
	return A;
}


AUTOMATE automate_concatenation(AUTOMATE A, AUTOMATE B){
	//les états du nouvel automate correspondent aux états de A puis ceux de B
	AUTOMATE C = automate_creer(A.Q + B.Q);
	//les états finaux de C sont les états finaux de B
	for(int i = 0; i< B.Q; i++)	C.F[i+A.Q] = B.F[i];
	//les transitions de C sont les transtions de A et de B 
	for(int i = 0; i< A.Q; i++){
		C.T[i] = copie_liste(A.T[i],0,1);
		if(A.F[i]) automate_ajouter_transition(C,i,-1,A.Q);
		//ajout des epsilons transitions des états finaux de A vers l'état initial de B
	}
	for(int i = 0; i< B.Q; i++)	C.T[i+A.Q] = copie_liste(B.T[i],A.Q,1);
	return C;
}

AUTOMATE automate_disjonction(AUTOMATE A, AUTOMATE B){
	//les états du nouvel automate correspondent à un état initial, puis aux états de A puis ceux de B
	AUTOMATE C = automate_creer(A.Q + B.Q +1);
	//les états finaux de C sont les états finaux de A et B
	for(int i = 0; i< A.Q; i++) C.F[i + 1] = A.F[i];
	for(int i = 0; i< B.Q; i++) C.F[i + A.Q + 1] = B.F[i];
	//les transitions de C sont les transtions de A et de B 
	for(int i = 0; i< A.Q; i++) C.T[i + 1] = copie_liste(A.T[i],1,1);
	for(int i = 0; i< B.Q; i++) C.T[i + A.Q + 1] = copie_liste(B.T[i],A.Q + 1,1);
	//ajout des epsilons transitions de l'état initial vers les états initiaux de A et B
	automate_ajouter_transition(C,0,-1,1);
	automate_ajouter_transition(C,0,-1,1 + A.Q);
	return C;
}

AUTOMATE automate_etoile(AUTOMATE A){
	//les états du nouvel automate correspondent à un état initial, puis les états de A 
	AUTOMATE B = automate_creer(A.Q + 1);
	//les transitions de B sont les transtions de A  
	for(int i = 0; i< A.Q; i++) B.T[i + 1] = copie_liste(A.T[i],1,1);
	//tous les états finaux de A ont une epsilon transition vers 0
	automate_ajouter_final(B,0);//l'état final de B est 0
	automate_ajouter_transition(B,0,-1,1);//transition epsilon entre le nouvel état initial et l'ancien
	for(int i = 0; i< A.Q; i++) {
		if(A.F[i])	automate_ajouter_transition(B,i + 1,-1,0);
	}
	return B;
}

int cherche_etat(ETATND p, int *ensemble_etat, int taille){//renvoie -1 si l'état n'est pas présent, le rang dans la liste sinon
	while(p && bcmp(p->ensemble_etat,ensemble_etat,taille*sizeof(int))){
		p = p->suiv;
	}
	if (p != NULL) return p->rang;
	return -1;
}

void liberer_etatnd(ETATND l){
	if(l){
		liberer_etatnd(l->suiv);
		free(l->ensemble_etat);
		liberer_transition(l->T);
		free(l);	
	}
}

AUTOMATE automate_determiniser(AUTOMATE A){
	AUTOMATE B = automate_supprimer_epsilon(A);
	//on stocke une liste d'ensemble états
	//un ensemble d'états est représentés par un tableau 
	ETATND l = malloc(sizeof(struct etatnd));//liste des états non déterministes
	l->ensemble_etat = calloc(B.Q,sizeof(int));
	l->ensemble_etat[0]=1; //état initial contient uniquement l'état initial de B
	l->T = NULL;
	l->rang = 0;
	l->suiv = NULL;

	int *nouvel_etat = malloc(B.Q*sizeof(int));//mémoire pour l'état construit à chaque fois
	ETATND a_traiter = l; //pointeur sur le prochain état à traiter
	ETATND fin = l;//pointeur sur la fin de la liste, pour insérer à la fin
	int nb_etats = 1;
	while(a_traiter){//on s'arrête quand il n'y a plus rien à traiter dans la liste des états
		for(char car = 'a'; car <= 'z'; car++){//on calcule toutes les transitions possibles
			memset(nouvel_etat,0,B.Q*sizeof(int));//remet à zéro l'état
			int non_vide = 0;//l'état est vide pour l'instant
			for(int i = 0; i<B.Q; i++){
				if(a_traiter->ensemble_etat[i]){//si l'état i fait partie de l'ensemble d'états, on cherche les transitions (i,car,*)
					TRANSITION T = B.T[i];
					while(T){
						if(T->car == car) {
							nouvel_etat[T->arr] = 1;
							non_vide =1; 
						}
						T = T->suiv;
					}
				}
			}//l'état obtenu en appliquant car à a_traiter->ensemble_etat est contenu dans nouvel_etat 
			if(non_vide){
				int rang = cherche_etat(l,nouvel_etat,B.Q);
				//recherche si l'état auquel on a accédé est nouveau, si c'est le cas on l'ajoute à la liste
				if(rang == -1){
					ETATND nouveau = malloc(sizeof(struct etatnd));//liste des états non déterministes
					nouveau->ensemble_etat = malloc(B.Q*sizeof(int));
					memcpy(nouveau->ensemble_etat,nouvel_etat,B.Q*sizeof(int));
					nouveau->T = NULL;
					rang = nb_etats;
					nouveau->rang = nb_etats++;
					nouveau->suiv = NULL;
					fin->suiv = nouveau; //on insère à la fin
					fin = nouveau;//on avance le pointeur de fin
				}
				//on ajoute la transition qu'on vient de calculer dans la liste des transitions
				TRANSITION nv_transition = malloc(sizeof(struct transition));
				nv_transition->car = car;
				nv_transition->arr = rang;
				nv_transition->suiv = a_traiter->T;
				a_traiter->T = nv_transition;
			}
		}
	a_traiter = a_traiter->suiv;
	}
	
	AUTOMATE C = automate_creer(nb_etats);//créé l'automate C avec comme état les ensembles d'états accessibles dans B
	//ajoute les transitions calculées à l'étape précédente
	ETATND l_debut = l;
	while(l){
		//teste si l->ensemble_etat contient un etat final et est donc final
		for(int i = 0; i < B.Q; i++) C.F[l->rang] |= l->ensemble_etat[i] && B.F[i];
		C.T[l->rang] = copie_liste(l->T,0,1);
		l = l->suiv;
	}
	automate_liberer_memoire(B);
	free(nouvel_etat);
	liberer_etatnd(l_debut);
	return C;
}
