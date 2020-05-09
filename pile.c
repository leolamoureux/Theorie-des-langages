#include "pile.h"

void affiche_state(STATE s){
	static const char *noms[] = {"S","A","B","C","D","E","F","CAR","(",")","+",".","*"};
	printf("%s|",noms[s]);
	s++;
}

PILE nouvelle_pile(int taille_max){
	PILE p;
	p.contenu = malloc(sizeof(STATE)*taille_max);
	if(!p.contenu) {printf("Plus de mémoire, malloc a échoué.\n"); exit(5);}
	p.sommet = 0;
	p.taille_max = taille_max;
	return p;
}

int est_vide(PILE p){
	return p.sommet == 0;
}

PILE empiler(PILE p, STATE s){
	if(p.sommet == p.taille_max){printf("Erreur pile pleine\n"); exit(0);} 
	p.contenu[p.sommet++] = s;
	return p;
}

STATE depiler(PILE *p){
	if(p->sommet == 0 ){printf("Erreur pile vide\n"); exit(0);} 
	return p->contenu[--p->sommet];
}

void affiche_pile(PILE p){
	printf("Pile de %d éléments: |",p.sommet);
	for(int i = 0; i < p.sommet; i++) affiche_state(p.contenu[i]);
	printf("\n");
}

void liberer_pile(PILE p){
	free(p.contenu);
}


