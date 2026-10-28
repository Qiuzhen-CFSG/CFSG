module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitarySection
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleCentralizer
/-!
# The nine-degree subgroup in the quadratic unitary octagon

Fong--Seitz's subgroup X replaces the two end unitary roots in the
five-root support by their centers. We construct it as the intersection
of that support with two actual Frattini preimages. Unique ordered root
coordinates then give the literal five-factor product and order 2^(9b).
The two end Frattini groups equal their centers for every positive degree,
including b=1 and either special/projective scalar convention.

The full Cartan normalizes X. Its commutator contains the middle unitary
root's Frattini group of order 2^b, and X contains the full cubic radical
centralizer. The original-factor and Chapter 12 applications are in the
matching CFSG modules and use the same marked quotient and full amalgam.

Source: Fong--Seitz I (1973), (6F), printed p.47, the paragraph defining X.
The exclusion of an invariant subgroup with projective unitary action,
the 2^(8b) representation bound and lower-central persistence remain
separate steps of that paragraph and its continuation.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
private theorem restriction_intersection {Y : Type*} [Group Y]
    (A N Z : Subgroup Y) (hZ : Z ≤ A) (hd : Disjoint A N)
    (hn : A ≤ normalizer (N : Set Y)) : A ⊓ (Z ⊔ N) = Z := by
  apply le_antisymm ?_ (le_inf hZ le_sup_left)
  intro x hx
  have hp : x ∈ (Z : Set Y)*(N : Set Y) := by
    rw [←coe_mul_of_left_le_normalizer_right Z N (hZ.trans hn)]
    exact hx.2
  obtain ⟨z,hz,n,hn,rfl⟩ := hp
  have hna : n ∈ A := by
    simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem (hZ hz)) hx.1
  change z*n ∈ Z
  rw [disjoint_def.mp hd hna hn,mul_one]
  exact hz

private theorem restrict_five {Y : Type*} [Group Y]
    (M A B C D E N₁ N₂ Z W : Subgroup Y)
    (hprod : (M : Set Y) = (A : Set Y)*((B : Set Y)*((C : Set Y)*((D : Set Y)*(E : Set Y)))))
    (hinj : Function.Injective (fun p : A × B × C × D × E =>
      (p.1 : Y)*((p.2.1 : Y)*((p.2.2.1 : Y)*((p.2.2.2.1 : Y)*(p.2.2.2.2 : Y))))))
    (hZ : Z ≤ A) (hW : W ≤ E)
    (hB₁ : B ≤ N₁) (hC₁ : C ≤ N₁) (hD₁ : D ≤ N₁) (hE₁ : E ≤ N₁)
    (hA₂ : A ≤ N₂) (hB₂ : B ≤ N₂) (hC₂ : C ≤ N₂) (hD₂ : D ≤ N₂)
    (hd₁ : Disjoint A N₁) (hd₂ : Disjoint E N₂)
    (hn₁ : A ≤ normalizer (N₁ : Set Y)) (hn₂ : E ≤ normalizer (N₂ : Set Y)) :
    let K := M ⊓ (Z ⊔ N₁) ⊓ (W ⊔ N₂)
    (K : Set Y) = (Z : Set Y)*((B : Set Y)*((C : Set Y)*((D : Set Y)*(W : Set Y)))) ∧
    Nat.card K = Nat.card Z * Nat.card B * Nat.card C * Nat.card D * Nat.card W := by
  dsimp only
  have he : (↑(M ⊓ (Z ⊔ N₁) ⊓ (W ⊔ N₂)) : Set Y) =
      (Z : Set Y)*((B : Set Y)*((C : Set Y)*((D : Set Y)*(W : Set Y)))) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxM : x ∈ (M : Set Y) := hx.1.1
      rw [hprod] at hxM
      obtain ⟨a,ha,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,he,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hxM
      have hrest₁ : b*(c*(d*e)) ∈ N₁ := mul_mem (hB₁ hb) (mul_mem (hC₁ hc) (mul_mem (hD₁ hd) (hE₁ he)))
      have ha' : a ∈ Z ⊔ N₁ := by
        simpa only [mul_inv_cancel_right] using (Z ⊔ N₁).mul_mem hx.1.2 (inv_mem (mem_sup_right hrest₁))
      have haZ : a ∈ Z := (restriction_intersection A N₁ Z hZ hd₁ hn₁) ▸ And.intro ha ha'
      have hrest₂ : a*(b*(c*d)) ∈ N₂ := mul_mem (hA₂ ha) (mul_mem (hB₂ hb) (mul_mem (hC₂ hc) (hD₂ hd)))
      have he' : e ∈ W ⊔ N₂ := by
        have hh := (W ⊔ N₂).mul_mem (inv_mem (mem_sup_right hrest₂)) hx.2
        simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hh
      have heW : e ∈ W := (restriction_intersection E N₂ W hW hd₂ hn₂) ▸ And.intro he he'
      exact ⟨a,haZ,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,heW,rfl⟩,rfl⟩,rfl⟩,rfl⟩
    · rintro _ ⟨a,ha,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,he,rfl⟩,rfl⟩,rfl⟩,rfl⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · change a*(b*(c*(d*e))) ∈ (M : Set Y)
        rw [hprod]
        exact ⟨a,hZ ha,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,hW he,rfl⟩,rfl⟩,rfl⟩,rfl⟩
      · exact mul_mem (mem_sup_left ha) (mem_sup_right (mul_mem (hB₁ hb)
          (mul_mem (hC₁ hc) (mul_mem (hD₁ hd) (hE₁ (hW he))))))
      · exact mul_mem (mem_sup_right (hA₂ (hZ ha))) (mul_mem (mem_sup_right (hB₂ hb))
          (mul_mem (mem_sup_right (hC₂ hc)) (mul_mem (mem_sup_right (hD₂ hd)) (mem_sup_left he))))
  refine ⟨he,?_⟩
  let f : Z × B × C × D × W → ↥(M ⊓ (Z ⊔ N₁) ⊓ (W ⊔ N₂)) := fun p =>
    ⟨p.1*(p.2.1*(p.2.2.1*(p.2.2.2.1*p.2.2.2.2))), by
      change _ ∈ (↑(M ⊓ (Z ⊔ N₁) ⊓ (W ⊔ N₂)) : Set Y)
      rw [he]
      exact ⟨p.1,p.1.property,_,⟨p.2.1,p.2.1.property,_,⟨p.2.2.1,p.2.2.1.property,_,
      ⟨p.2.2.2.1,p.2.2.2.1.property,p.2.2.2.2,p.2.2.2.2.property,rfl⟩,rfl⟩,rfl⟩,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have hh := hinj (a₁ := (inclusion hZ p.1,p.2.1,p.2.2.1,p.2.2.2.1,inclusion hW p.2.2.2.2))
        (a₂ := (inclusion hZ q.1,q.2.1,q.2.2.1,q.2.2.2.1,inclusion hW q.2.2.2.2))
        (congrArg Subtype.val hpq)
      have h0 := congrArg (fun t : A × B × C × D × E => t.1) hh
      have h1 := congrArg (fun t : A × B × C × D × E => t.2.1) hh
      have h2 := congrArg (fun t : A × B × C × D × E => t.2.2.1) hh
      have h3 := congrArg (fun t : A × B × C × D × E => t.2.2.2.1) hh
      have h4 := congrArg (fun t : A × B × C × D × E => t.2.2.2.2) hh
      exact Prod.ext ((inclusion_injective hZ) h0) (Prod.ext h1 (Prod.ext h2
        (Prod.ext h3 ((inclusion_injective hW) h4))))
    · intro x
      have hx : (x : Y) ∈ (↑(M ⊓ (Z ⊔ N₁) ⊓ (W ⊔ N₂)) : Set Y) := x.property
      rw [he] at hx
      obtain ⟨a,ha,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,he,hde⟩,hcd⟩,hbc⟩,hab⟩ := hx
      refine ⟨(⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩,⟨e,he⟩),Subtype.ext ?_⟩
      change a*(b*(c*(d*e))) = x
      exact (congrArg (fun z => a*(b*(c*z))) hde).trans
        ((congrArg (fun z => a*(b*z)) hcd).trans ((congrArg (fun z => a*z) hbc).trans hab))
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_prod,Nat.card_prod,Nat.card_prod,Nat.card_prod]
  ac_rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem middle_five_coordinates (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j) :
    let A := rootAt Q split j (Q.simple i)
    let B := rootAt Q split i (Q.simple j*Q.simple i)
    let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    let D := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    let E := rootAt Q split j (Q.simple i*Q.simple j)
    (middleFive Q split j i : Set (X ⧸ Q.D)) =
      (A : Set _)*((B : Set _)*((C : Set _)*((D : Set _)*(E : Set _)))) ∧
    Function.Injective (fun p : A × B × C × D × E =>
      (p.1 : X ⧸ Q.D)*((p.2.1 : X ⧸ Q.D)*((p.2.2.1 : X ⧸ Q.D)*
        ((p.2.2.2.1 : X ⧸ Q.D)*(p.2.2.2.2 : X ⧸ Q.D))))) := by
  obtain ⟨b,he,hlist⟩ := five_intersection Q split hm j i hij.symm
  let n : X ⧸ Q.D := representative (Q.simple i)
  have hl : (orderedRoots Q split b 5).map (fun A => rightConjugate A n) =
      [rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i),
       rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
       rootAt Q split i (Q.simple j*Q.simple i*Q.simple j),
       rootAt Q split j (Q.simple i*Q.simple j)] := by
    rw [hlist]
    simp only [List.map_cons,List.map_nil,n,right_simple,right_rep,mul_assoc,ssq,mul_one]
    simp only [←mul_assoc,fourth_root Q split hm i j hij]
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b 5)) := by
    intro p q heq
    apply (orderedCoordinates Q split b 5 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using heq
  have hi : Function.Injective (rootProduct ((orderedRoots Q split b 5).map
      (fun A => rightConjugate A n))) := by
    intro p q hpq
    obtain ⟨p,rfl⟩ := (conjugateTuple (orderedRoots Q split b 5) n).surjective p
    obtain ⟨q,rfl⟩ := (conjugateTuple (orderedRoots Q split b 5) n).surjective q
    rw [rootProduct_conjugateTuple,rootProduct_conjugateTuple] at hpq
    exact congrArg _ (hinj (mul_left_cancel (mul_right_cancel hpq)))
  have hrange : Set.range (rootProduct ((orderedRoots Q split b 5).map
      (fun A => rightConjugate A n))) = (middleFive Q split j i : Set _) := by
    ext x
    rw [he]
    constructor
    · rintro ⟨p,rfl⟩
      obtain ⟨p,rfl⟩ := (conjugateTuple (orderedRoots Q split b 5) n).surjective p
      rw [rootProduct_conjugateTuple]
      change n*(n⁻¹*rootProduct _ p*n)*n⁻¹ ∈ rootIntersection split (longest Q) (alternatingWord Q b 5)⁻¹
      simp only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
      rw [←orderedCoordinates_apply Q split b 5 (by omega)]
      exact (orderedCoordinates Q split b 5 (by omega) p).property
    · intro hx
      obtain ⟨p,hp⟩ := (orderedCoordinates Q split b 5 (by omega)).surjective ⟨n*x*n⁻¹,hx⟩
      refine ⟨conjugateTuple (orderedRoots Q split b 5) n p,?_⟩
      rw [rootProduct_conjugateTuple,←orderedCoordinates_apply Q split b 5 (by omega)]
      have hh := congrArg Subtype.val hp
      rw [hh]
      simp only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
  rw [hl] at hi hrange
  constructor
  · have hp := hrange.symm.trans (rootProduct_range _)
    change (middleFive Q split j i : Set (X ⧸ Q.D)) =
      (rootAt Q split j (Q.simple i) : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set _)*
      ((rootAt Q split j (Q.simple i*Q.simple j) : Set _)*1)))) at hp
    simpa only [mul_one] using hp
  · intro p q hpq
    have hh := hi (a₁ := (p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2,PUnit.unit))
      (a₂ := (q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2,PUnit.unit))
      (by simpa only [rootProduct,mul_one] using hpq)
    exact congrArg (fun t => (t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1)) hh


private theorem shifted_root_le (k j : Fin 2) (v w : Weyl Q)
    (hU : Q.tits.wordLength ((w*v⁻¹)*Q.simple k)=Q.tits.wordLength (w*v⁻¹)+1)
    (hV : Q.tits.wordLength ((Q.simple j*(w*v⁻¹))*Q.simple k)=
      Q.tits.wordLength (Q.simple j*(w*v⁻¹))+1) :
    rootAt Q split k v ≤ rightConjugate (simpleRemainder Q split j)
      (representative w : X ⧸ Q.D) := by
  have hu : Q.tits.wordLength ((v*w⁻¹)⁻¹*Q.simple k)=Q.tits.wordLength (v*w⁻¹)⁻¹+1 := by
    simpa only [mul_inv_rev,inv_inv] using hU
  have hv : Q.tits.wordLength ((Q.simple j*(v*w⁻¹)⁻¹)*Q.simple k)=
      Q.tits.wordLength (Q.simple j*(v*w⁻¹)⁻¹)+1 := by
    simpa only [mul_inv_rev,inv_inv] using hV
  have hh := comap_mono (f := (MulAut.conj (representative w : X ⧸ Q.D)).toMonoidHom)
    (rootAt_le_remainder Q split k j (v*w⁻¹) hu hv)
  change rightConjugate (rootAt Q split k (v*w⁻¹)) _ ≤ _ at hh
  rwa [rootAt_right Q split k (v*w⁻¹) w _ (representative_spec _),inv_mul_cancel_right] at hh

private theorem shifted_root_disjoint (j : Fin 2) (w : Weyl Q) :
    Disjoint (rootAt Q split j w) (rightConjugate (simpleRemainder Q split j)
      (representative w : X ⧸ Q.D)) := by
  apply disjoint_def.mpr
  intro x hx hy
  apply (MulAut.conj (representative w : X ⧸ Q.D)).injective
  exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split j) hx hy).trans (map_one _).symm

private theorem shifted_root_normalizes (j : Fin 2) (w : Weyl Q)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    rootAt Q split j w ≤ normalizer (rightConjugate (simpleRemainder Q split j)
      (representative w : X ⧸ Q.D) : Set _) := by
  have h := (simpleRoot_le Q split j).trans (split.U_le.trans
    ((Q.tits.B_le_standardParabolic _).trans (remainder_parabolic_normalizes Q split j hKj)))
  exact (comap_mono h).trans (le_normalizer_comap _)

private theorem eight_containments (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j) :
    let N₁ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i) : X ⧸ Q.D)
    let N₂ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)
    rootAt Q split i (Q.simple j*Q.simple i) ≤ N₁ ∧
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ N₁ ∧
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ N₁ ∧
    rootAt Q split j (Q.simple i*Q.simple j) ≤ N₁ ∧
    rootAt Q split j (Q.simple i) ≤ N₂ ∧
    rootAt Q split i (Q.simple j*Q.simple i) ≤ N₂ ∧
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ N₂ ∧
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ N₂ := by
  have hlen (b : Bool) (n : ℕ) (hn : n ≤ 8) : Q.tits.wordLength (alternatingWord Q b n)=n :=
    wordLength_alternatingWord Q b (hm ▸ hn)
  have h0 := Q.tits.wordLength_one
  have h1 := octagon_lengths Q i hm j hij
  have h2 := octagon_lengths Q j hm i hij.symm
  have hs (k : Fin 2) : (Q.simple k)⁻¹=Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)
  have h6i : Q.tits.wordLength (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j)=6 := by
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
      rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen false 6 (by decide)
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen true 6 (by decide)
    · exact (hij rfl).elim
  have h6j : Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i)=6 := by
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
      rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen true 6 (by decide)
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen false 6 (by decide)
    · exact (hij rfl).elim
  have h7j : Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j)=7 := by
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl <;>
      rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen true 7 (by decide)
    · simpa only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
        mul_one,mul_assoc] using hlen false 7 (by decide)
    · exact (hij rfl).elim
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply shifted_root_le
    all_goals
      simp only [mul_inv_rev,hs,mul_assoc,←mul_assoc (Q.simple i) (Q.simple i),
        ←mul_assoc (Q.simple j) (Q.simple j),ssq,one_mul]
      simp only [←mul_assoc,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2,
        h2.1,h2.2.1,h2.2.2.1,h2.2.2.2.1,h2.2.2.2.2,h0,h6i,h6j,h7j]


/-- The literal five-factor subgroup X of Fong--Seitz I (6F), p.47.
Only its two end unitary roots are replaced by their Frattini subgroups. -/
@[expose] def unitaryNineSubgroup (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  rootFrattiniAt Q split j (Q.simple i) ⊔
    rootAt Q split i (Q.simple j*Q.simple i) ⊔
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊔
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
    rootFrattiniAt Q split j (Q.simple i*Q.simple j)

private theorem subgroup_of_product {Y : Type*} [Group Y]
    (K A B C D E : Subgroup Y)
    (hp : (K : Set Y)=(A : Set Y)*((B : Set Y)*((C : Set Y)*((D : Set Y)*(E : Set Y))))) :
    K=A ⊔ B ⊔ C ⊔ D ⊔ E := by
  have hroot (F : Subgroup Y) (hf : F=A ∨ F=B ∨ F=C ∨ F=D ∨ F=E) : F ≤ K := by
    intro x hx
    change x ∈ (K : Set Y)
    rw [hp]
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact ⟨x,hx,1,⟨1,one_mem _,1,⟨1,one_mem _,1,⟨1,one_mem _,1,one_mem _,by simp⟩,by simp⟩,by simp⟩,by simp⟩
    · exact ⟨1,one_mem _,x,⟨x,hx,1,⟨1,one_mem _,1,⟨1,one_mem _,1,one_mem _,by simp⟩,by simp⟩,by simp⟩,by simp⟩
    · exact ⟨1,one_mem _,x,⟨1,one_mem _,x,⟨x,hx,1,⟨1,one_mem _,1,one_mem _,by simp⟩,by simp⟩,by simp⟩,by simp⟩
    · exact ⟨1,one_mem _,x,⟨1,one_mem _,x,⟨1,one_mem _,x,⟨x,hx,1,one_mem _,by simp⟩,by simp⟩,by simp⟩,by simp⟩
    · exact ⟨1,one_mem _,x,⟨1,one_mem _,x,⟨1,one_mem _,x,⟨1,one_mem _,x,hx,by simp⟩,by simp⟩,by simp⟩,by simp⟩
  apply le_antisymm ?_ (sup_le (sup_le (sup_le (sup_le
    (hroot A (by tauto)) (hroot B (by tauto))) (hroot C (by tauto)))
      (hroot D (by tauto))) (hroot E (by tauto)))
  intro x hx
  have hx' : x ∈ (K : Set Y) := hx
  rw [hp] at hx'
  obtain ⟨a,ha,_,⟨b,hb,_,⟨c,hc,_,⟨d,hd,e,he,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hx'
  exact mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left ha))))
    (mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right hb))))
      (mul_mem (mem_sup_left (mem_sup_left (mem_sup_right hc)))
        (mul_mem (mem_sup_left (mem_sup_right hd)) (mem_sup_right he))))

/-- X is the intersection of the middle five roots with the two actual
end-coordinate Frattini preimages. -/
theorem unitaryNineSubgroup_intersection (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    unitaryNineSubgroup Q split i j =
      middleFive Q split j i ⊓
        (rootFrattiniAt Q split j (Q.simple i) ⊔
          rightConjugate (simpleRemainder Q split j) (representative (Q.simple i) : X ⧸ Q.D)) ⊓
        (rootFrattiniAt Q split j (Q.simple i*Q.simple j) ⊔
          rightConjugate (simpleRemainder Q split j) (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)) := by
  obtain ⟨hp,hi⟩ := middle_five_coordinates Q split hm i j hij
  obtain ⟨hB₁,hC₁,hD₁,hE₁,hA₂,hB₂,hC₂,hD₂⟩ := eight_containments Q split hm i j hij
  obtain ⟨he,_⟩ := restrict_five _ _ _ _ _ _ _ _
    (rootFrattiniAt Q split j (Q.simple i)) (rootFrattiniAt Q split j (Q.simple i*Q.simple j))
    hp hi (map_subtype_le _) (map_subtype_le _) hB₁ hC₁ hD₁ hE₁ hA₂ hB₂ hC₂ hD₂
    (shifted_root_disjoint Q split j _) (shifted_root_disjoint Q split j _)
    (shifted_root_normalizes Q split j _ hKj) (shifted_root_normalizes Q split j _ hKj)
  exact (subgroup_of_product _ _ _ _ _ _ he).symm

/-- Unique coordinates give the exact ordered product and cardinality of X. -/
theorem unitaryNineSubgroup_product_card (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (unitaryNineSubgroup Q split i j : Set (X ⧸ Q.D)) =
      (rootFrattiniAt Q split j (Q.simple i) : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set _)*
      (rootFrattiniAt Q split j (Q.simple i*Q.simple j) : Set _)))) ∧
    Nat.card (unitaryNineSubgroup Q split i j) =
      Nat.card (rootFrattiniAt Q split j (Q.simple i))*Nat.card (simpleRoot Q split i)*
      Nat.card (simpleRoot Q split j)*Nat.card (simpleRoot Q split i)*
      Nat.card (rootFrattiniAt Q split j (Q.simple i*Q.simple j)) := by
  obtain ⟨hp,hi⟩ := middle_five_coordinates Q split hm i j hij
  obtain ⟨hB₁,hC₁,hD₁,hE₁,hA₂,hB₂,hC₂,hD₂⟩ := eight_containments Q split hm i j hij
  have hh := restrict_five _ _ _ _ _ _ _ _
    (rootFrattiniAt Q split j (Q.simple i)) (rootFrattiniAt Q split j (Q.simple i*Q.simple j))
    hp hi (map_subtype_le _) (map_subtype_le _) hB₁ hC₁ hD₁ hE₁ hA₂ hB₂ hC₂ hD₂
    (shifted_root_disjoint Q split j _) (shifted_root_disjoint Q split j _)
    (shifted_root_normalizes Q split j _ hKj) (shifted_root_normalizes Q split j _ hKj)
  dsimp only at hh
  rw [←unitaryNineSubgroup_intersection Q split hm i j hij hKj] at hh
  exact ⟨hh.1,by simpa only [rootAt,card_rightConjugate] using hh.2⟩

/-- The product has exactly the centers at its two ends, as in the
source definition of X; the intrinsic subgroups are mapped into the
original ambient quotient before multiplying. -/
theorem unitaryNineSubgroup_center_product
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    (unitaryNineSubgroup Q split i j : Set (X ⧸ Q.D)) =
      ((center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set _)*
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set _)*
      ((center (rootAt Q split j (Q.simple i*Q.simple j))).map
        (rootAt Q split j (Q.simple i*Q.simple j)).subtype : Set _)))) := by
  have hp := (unitaryNineSubgroup_product_card Q split hm i j hij hKj).1
  simpa only [rootFrattiniAt,
    unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ] using hp

/-- X is a subgroup of the same five-root support of the derived radical. -/
theorem unitaryNineSubgroup_le_middleFive (i j : Fin 2) :
    unitaryNineSubgroup Q split i j ≤ middleFive Q split j i := by
  exact sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup (map_subtype_le _) le_rfl) le_rfl) le_rfl)
    (map_subtype_le _)

/-- Each unitary Frattini root has the fixed-field order, for arbitrary
Hermitian form and including degree one. -/
theorem unitary_rootFrattini_card
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) : Nat.card (rootFrattiniAt Q split j w)=2^b := by
  rw [rootFrattiniAt,card_map_of_injective (rootAt Q split j w).subtype_injective,
    unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ w]
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨ep⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  exact QuadrangleStructure.unitary_cross_center_card Q split J₀ hb hcard hf rfl j w hKj (μ.trans ep)

/-- The source subgroup has exactly 2^(9b) elements in the quadratic
unitary branch; no representation-degree bound is used. -/
theorem unitaryNineSubgroup_card
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i)=2^(2*b))
    (hj : Nat.card (simpleRoot Q split j)=(2^b)^3) :
    Nat.card (unitaryNineSubgroup Q split i j)=2^(9*b) := by
  rw [(unitaryNineSubgroup_product_card Q split hm i j hij hKj).2,
    unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ,
    unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ,hi,hj,
    ←pow_mul,←pow_add,←pow_add,←pow_add,←pow_add]
  congr 1
  omega


/-- The full Cartan normalizes X, including its two intrinsic Frattini factors. -/
theorem unitaryNineSubgroup_cartan_normalizes (i j : Fin 2) :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (unitaryNineSubgroup Q split i j : Set (X ⧸ Q.D)) := by
  have hphi (w : Weyl Q) : Q.tits.B ⊓ Q.tits.N ≤
      normalizer (rootFrattiniAt Q split j w : Set (X ⧸ Q.D)) :=
    (rootAt_torus_normalizes Q split j w).trans
      (normalizer_le_normalizer_characteristic_image _ (frattini _))
  have join (A B : Subgroup (X ⧸ Q.D))
      (hA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set _))
      (hB : Q.tits.B ⊓ Q.tits.N ≤ normalizer (B : Set _)) :
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (↑(A ⊔ B) : Set _) :=
    (le_inf hA hB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  exact join _ _ (join _ _ (join _ _ (join _ _ (hphi _)
    (rootAt_torus_normalizes Q split i _)) (rootAt_torus_normalizes Q split j _))
      (rootAt_torus_normalizes Q split i _)) (hphi _)

/-- The middle unitary root supplies the source's nontrivial commutator
inside X: its Frattini group is contained in the actual ambient [X,X]. -/
theorem unitaryNineSubgroup_commutator_contains
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (i j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤
      ⁅unitaryNineSubgroup Q split i j,unitaryNineSubgroup Q split i j⁆ := by
  rw [unitary_rootFrattini_eq_commutator Q split J hb hcard hconj j hKj μ]
  have hC : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤
      unitaryNineSubgroup Q split i j := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  exact commutator_mono hC hC

/-- The previously constructed full cubic radical centralizer lies in X,
with the same literal root factors and scalar conventions. -/
theorem unitary_cubic_radical_le_nine (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j)
    (hfree : ∀ w : Weyl Q, rootAt Q split i w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w : Weyl Q, rootAt Q split j w ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = rootFrattiniAt Q split j w) :
    simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      unitaryNineSubgroup Q split i j := by
  intro x hx
  have hx' : x ∈ (↑(simpleRemainder Q split j ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) : Set (X ⧸ Q.D)) := hx
  rw [unitary_cubic_radical_product Q split hm i j hij hfree hfix] at hx'
  obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hx'
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left ha))))
    (mem_sup_left (mem_sup_left (mem_sup_right (map_subtype_le _ hb))))) (mem_sup_right hc)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
