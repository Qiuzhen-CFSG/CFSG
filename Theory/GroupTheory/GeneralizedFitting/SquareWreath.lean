module
public import Theory.GroupTheory.AutomorphismSquareWreath
public import Theory.GroupTheory.AutomorphismSquareOuterTwo
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SylowOuterCover
public import Theory.GroupTheory.TwoOrbitThree.Quotient

/-!
# Faithful wreath actions of a generalized Fitting square

A centerless square equal to F* has trivial ambient centralizer. Conjugation
therefore embeds the ambient group in the automorphism wreath product, with
explicit formulas for the two inner factors. If the factor outer group is a
two-group, the same square and any Sylow two-subgroup generate the group.

For two exchanged C-components these facts apply in the literal quotient by
the ambient two-core. The two product coordinates retain the given exchanger;
the Sylow supplement then lifts back through the same quotient map.

Source application: Aschbacher--Smith, proof of 14.6.14 and the strict-closure
branch of 14.6.16, printed pp.1033,1035. Determining the full outer image is a
separate step; a faithful embedding is not asserted to be surjective.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.AutomorphismSquare
open WreathTwoElementaryRank
variable {G S : Type*} [Group G] [Group S]
variable (N : Subgroup G) [N.Normal]

/-- Conjugation on the normal square, in the prescribed product coordinates. -/
@[expose] def squareConjugation (e : N ≃* S × S) : G →* MulAut (S × S) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem squareConjugation_inner (e : N ≃* S × S) (x : N) :
    squareConjugation N e (x : G) = MulAut.conj (e x) := by
  change MulAut.congr e (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

variable [Finite S] [IsQuasisimple S]

/-- The same conjugation action in the literal regular wreath product. -/
@[expose] def wreathConjugation (e : N ≃* S × S) (hz : center S = ⊥) :
    G →* RegularWreathProduct (MulAut S) (Multiplicative (ZMod 2)) :=
  (wreathEquiv hz).symm.toMonoidHom.comp (squareConjugation N e)

theorem wreathConjugation_inner (e : N ≃* S × S) (hz : center S = ⊥) (x : N) :
    wreathConjugation N e hz (x : G) =
      baseHom (MulAut.conj (e x).1, MulAut.conj (e x).2) := by
  apply (wreathEquiv hz).injective
  change wreathEquiv hz ((wreathEquiv hz).symm (squareConjugation N e x)) = _
  rw [MulEquiv.apply_symm_apply, squareConjugation_inner, wreathEquiv_apply,
    wreathHom_inner]

theorem wreathConjugation_injective (e : N ≃* S × S) (hz : center S = ⊥)
    (hc : centralizer (N : Set G) = ⊥) :
    Function.Injective (wreathConjugation N e hz) :=
  (wreathEquiv hz).symm.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot N hc))

omit [N.Normal] in
theorem square_outer_isTwoGroup (e : N ≃* S × S) (hz : center S = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer S)) : IsPGroup 2 (MulAut.Outer N) :=
  (outer_isPGroup_two hz ho).of_equiv (MulAut.outerCongr e).symm

variable [Finite G]

omit [N.Normal] [Finite S] [IsQuasisimple S] in
/-- A centerless square that is F* has trivial ambient centralizer. -/
theorem square_layer_centralizer (e : N ≃* S × S) (hz : center S = ⊥)
    (hN : N = generalizedFitting G) : centralizer (N : Set G) = ⊥ := by
  have hzN : center N = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center (S × S) := (centerCongr e ⟨x,hx⟩).property
    rw [Subgroup.center_prod,hz,bot_prod_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hCN : centralizer (N : Set G) ≤ N := by
    rw [hN]
    exact centralizer_generalizedFitting_le G
  apply bot_unique
  intro x hx
  have hxc : (⟨x,hCN hx⟩ : N) ∈ center N := mem_center_iff.mpr fun y =>
    Subtype.ext (hx y y.property)
  exact congrArg Subtype.val (show (⟨x,hCN hx⟩ : N) = 1 from mem_bot.mp (hzN ▸ hxc))

/-- Faithfulness and the inner-coordinate formula for the literal wreath action. -/
theorem square_layer_wreath_action (e : N ≃* S × S) (hz : center S = ⊥)
    (hN : N = generalizedFitting G) :
    Function.Injective (wreathConjugation N e hz) ∧
      ∀ x : N, wreathConjugation N e hz (x : G) =
        baseHom (MulAut.conj (e x).1, MulAut.conj (e x).2) :=
  ⟨wreathConjugation_injective N e hz (square_layer_centralizer N e hz hN),
    wreathConjugation_inner N e hz⟩

/-- The same square has a two-group ambient quotient, and any Sylow two-subgroup
supplements it. No surjectivity onto the automorphism wreath is asserted. -/
theorem square_layer_two_extension (e : N ≃* S × S) (hz : center S = ⊥)
    (hN : N = generalizedFitting G) (ho : IsPGroup 2 (MulAut.Outer S))
    (T : Sylow 2 G) : IsPGroup 2 (G ⧸ N) ∧ N ⊔ (T : Subgroup G) = ⊤ := by
  have hc := square_layer_centralizer N e hz hN
  have hout := square_outer_isTwoGroup N e hz ho
  refine ⟨hout.of_injective (MulAut.outerAction N) (MulAut.outerAction_injective N hc),?_⟩
  simpa only [hc,sup_bot_eq] using sup_centralizer_sup_sylow_eq_top N hout T

end Theory.GroupTheory.AutomorphismSquare

namespace Theory.GroupTheory.AutomorphismSquare
open Subgroup WreathTwoElementaryRank
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsQuasisimple S]

/-- A specified exchanged component pair gives the faithful wreath action on
the literal ambient two-core quotient, with both factor coordinates retained. -/
theorem exchanged_cComponent_layer_action
    (L : Subgroup G) (hL : L.IsCComponent) (t : G)
    (ht : t ∉ normalizer (L : Set G))
    (e : L.map (QuotientGroup.mk' (pCore 2 G)) ≃* S)
    (hz : center S = ⊥) (ho : IsPGroup 2 (MulAut.Outer S))
    (hF : (L ⊔ L.conjBy t).map (QuotientGroup.mk' (pCore 2 G)) =
      generalizedFitting (G ⧸ pCore 2 G)) (T : Sylow 2 G) :
    (L ⊔ L.conjBy t) ⊔ (T : Subgroup G) = ⊤ ∧
    let q := QuotientGroup.mk' (pCore 2 G)
    let A := L.map q
    let K := (L ⊔ L.conjBy t).map q
    ∃ k : K ≃* S × S,
      (∀ x : A, (k.symm (e x,1) : G ⧸ pCore 2 G) = x) ∧
      (∀ x : A, (k.symm (1,e x) : G ⧸ pCore 2 G) = q t * x * (q t)⁻¹) ∧
      ∃ ρ : (G ⧸ pCore 2 G) →* RegularWreathProduct (MulAut S) (Multiplicative (ZMod 2)),
        Function.Injective ρ ∧
        (∀ x : K, ρ x = baseHom (MulAut.conj (k x).1, MulAut.conj (k x).2)) ∧
        ∀ g (x : K), (k.symm (wreathHom (ρ g) (k x)) : G ⧸ pCore 2 G) =
          g * x * g⁻¹ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := L.map q
  let K := (L ⊔ L.conjBy t).map q
  let : IsQuasisimple (L ⧸ pCore 2 L) :=
    IsQuasisimple.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hL).trans e).symm
  have hc := TwoOrbitThree.quotient_pair_commutes hL t ht
  have hzA : center A = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center S := (centerCongr e ⟨x,hx⟩).property
    rw [hz,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hd : Disjoint A (A.conjBy (q t)) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hxc : (⟨x,hx⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hy).symm)
    exact congrArg Subtype.val (show (⟨x,hx⟩ : A) = 1 from mem_bot.mp (hzA ▸ hxc))
  obtain ⟨ep,hep⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A _ hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  let et : A ≃* A.conjBy (q t) := (MulAut.conj (q t)).subgroupMap A
  have hK : K = A ⊔ A.conjBy (q t) := TwoOrbitThree.pair_map_quotient L t _
  let k : K ≃* S × S := (MulEquiv.subgroupCongr hK).trans
    (ep.symm.trans (e.prodCongr (et.symm.trans e)))
  have hk (x y : A) : (k.symm (e x,e y) : G ⧸ pCore 2 G) =
      (x : G ⧸ pCore 2 G) * (q t * y * (q t)⁻¹) := by
    change (ep (e.symm (e x), et (e.symm (e y))) : G ⧸ pCore 2 G) = _
    rw [e.symm_apply_apply,e.symm_apply_apply]
    exact hep x (et y)
  change K = generalizedFitting (G ⧸ pCore 2 G) at hF
  let : K.Normal := hF.symm ▸ inferInstance
  obtain ⟨_,hgen⟩ := square_layer_two_extension K k hz hF ho
    (T.mapSurjective (QuotientGroup.mk'_surjective _))
  have hgenG : (L ⊔ L.conjBy t) ⊔ (T : Subgroup G) = ⊤ := by
    have hm : ((L ⊔ L.conjBy t) ⊔ (T : Subgroup G)).map q = ⊤ := by
      rw [Subgroup.map_sup]
      exact hgen
    have hcore : q.ker ≤ (L ⊔ L.conjBy t) ⊔ (T : Subgroup G) := by
      rw [QuotientGroup.ker_mk']
      exact (pCore_isPGroup.le_sylow_of_normal T).trans le_sup_right
    have hh := congrArg (comap q) hm
    simpa only [comap_map_eq_self hcore,comap_top] using hh
  refine ⟨hgenG,k,?_,?_,wreathConjugation K k hz,
    (square_layer_wreath_action K k hz hF).1,wreathConjugation_inner K k hz,?_⟩
  · intro x
    simpa only [map_one,coe_one,mul_one,mul_inv_cancel] using hk x 1
  · intro x
    simpa only [map_one,coe_one,one_mul] using hk 1 x
  · intro g x
    change (k.symm (wreathHom ((wreathEquiv hz).symm (squareConjugation K k g)) (k x)) :
      G ⧸ pCore 2 G) = _
    rw [←wreathEquiv_apply hz, MulEquiv.apply_symm_apply]
    change (k.symm (k ((MulAut.conjNormal g) (k.symm (k x)))) : G ⧸ pCore 2 G) = _
    rw [k.symm_apply_apply,k.symm_apply_apply]
    rfl

end Theory.GroupTheory.AutomorphismSquare
