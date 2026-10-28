module
public import Theory.GroupTheory.CommutingProductOddAxes
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.TorusCoordinates
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.Center
/-!
# The actual original Hall torus axes lie in the original blocks

The opposite coordinate kernel in the commuting component has exponent
two, by the centerless short-block calculation. An odd subgroup cannot
retain that component. This lifts both literal kernel axes of the original
A₅ product projection into L and its prescribed T-conjugate. The original
local block and fixed-center hypotheses also give their orders, disjointness
and product, with no choice of orientation.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

/-- Both odd quotient axes lift to the prescribed actual factors. -/
theorem source_original_odd_axes_le_factors
    (hcomm : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcore : IsElementaryAbelian 2 (pCore 2 L))
    (C : Subgroup G) (hCR : C ≤ localOrbit T L) (hodd : Odd (Nat.card C)) :
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    ((MonoidHom.snd _ _).comp q).ker.map C.subtype ≤ L ∧
      ((MonoidHom.fst _ _).comp q).ker.map C.subtype ≤ L.map (MulAut.conj t).toMonoidHom := by
  let R := localOrbit T L
  let J := L.map (MulAut.conj t).toMonoidHom
  let q := originalA5ProductProjection D e hn ht htn
  have hgen : L ⊔ J = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hJL : J ≤ R := hgen ▸ le_sup_right
  have hL : L ≤ R := le_componentOrbit L T
  have hpow (l : L) (hl : e (QuotientGroup.mk' (pCore 2 L) l) = 1) : (l:G)^2=1 := by
    have hl' : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp (e.map_eq_one_iff.mp hl)
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hcore.exponent_dvd_p
      (⟨l,hl'⟩ : pCore 2 L)
    exact congrArg (fun x : pCore 2 L => ((x:L):G)) hh
  let P := ((MonoidHom.snd _ _).comp (q.comp (inclusion hCR))).ker.map C.subtype
  let Q := ((MonoidHom.fst _ _).comp (q.comp (inclusion hCR))).ker.map C.subtype
  have hPC : P ≤ C := map_subtype_le _
  have hQC : Q ≤ C := map_subtype_le _
  have hPR := hPC.trans hCR
  have hQR := hQC.trans hCR
  constructor
  · apply odd_subgroup_le_commuting_factor_of_relative_axis L J P R
      (hodd.of_dvd_nat (card_dvd_of_le hPC)) hcomm hgen hPR ((MonoidHom.snd _ _).comp q)
    · intro l
      change (q ⟨l,_⟩).2=1
      rw [originalA5ProductProjection_first]
    · intro p
      obtain ⟨c,hc,he⟩ := p.property
      have hh : (q ⟨c,hCR c.property⟩).2=1 := hc
      have hcp : (⟨c,hCR c.property⟩ : R)=⟨p,hPR p.property⟩ := Subtype.ext he
      change (q ⟨p,hPR p.property⟩).2=1
      rw [←hcp]
      exact hh
    · intro j hj
      obtain ⟨l,hl,he⟩ := j.property
      have he' : (⟨j,hJL j.property⟩ : R)= originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L) :=
        Subtype.ext he.symm
      change (q ⟨j,_⟩).2=1 at hj
      rw [he',originalA5ProductProjection_second] at hj
      have hp := congrArg (MulAut.conj t) (hpow ⟨l,hl⟩ hj)
      have heG : (MulAut.conj t) l=(j:G) := he
      simpa only [map_pow,map_one,heG] using hp
  · apply odd_subgroup_le_commuting_factor_of_relative_axis J L Q R
      (hodd.of_dvd_nat (card_dvd_of_le hQC)) (le_centralizer_iff.mp hcomm)
      (sup_comm L J ▸ hgen) hQR ((MonoidHom.fst _ _).comp q)
    · intro j
      obtain ⟨l,hl,he⟩ := j.property
      have he' : (⟨j,hJL j.property⟩ : R)= originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L) :=
        Subtype.ext he.symm
      change (q ⟨j,_⟩).1=1
      rw [he',originalA5ProductProjection_second]
    · intro p
      obtain ⟨c,hc,he⟩ := p.property
      have hh : (q ⟨c,hCR c.property⟩).1=1 := hc
      have hcp : (⟨c,hCR c.property⟩ : R)=⟨p,hQR p.property⟩ := Subtype.ext he
      change (q ⟨p,hQR p.property⟩).1=1
      rw [←hcp]
      exact hh
    · intro l hl
      change (q ⟨l,_⟩).1=1 at hl
      rw [originalA5ProductProjection_first] at hl
      exact hpow l hl


include D in
/-- The original local block commutes with its prescribed distinct conjugate. -/
theorem source_original_block_commutes_prescribed_conjugate
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let X := localJoin T L
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  let tX : X := ⟨t,(show (T : Subgroup G) ≤ X from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tX).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tX)
  have hmapA : A.map X.subtype=L := map_subgroupOf_eq_of_le hLX
  have hmapB : B.map X.subtype=L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tX).toMonoidHom from rfl,map_map]
    rw [show X.subtype.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map X.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (subgroupOfEquivOfLe hLX).symm (pCore_map_iso 2 (subgroupOfEquivOfLe hLX).symm))
  have hc := congrArg (map X.subtype) (hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne)
  rw [map_commutator,hmapA,hmapB,Subgroup.map_bot] at hc
  exact commutator_eq_bot_iff_le_centralizer.mp hc


/-- The two literal source torus axes, with all factor and order data. -/
theorem source_original_borel_torus_axes
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (C : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C=9) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    let D₁ := ((MonoidHom.snd _ _).comp q).ker.map C.subtype
    let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C.subtype
    D₁ ≤ L ∧ D₂ ≤ L.map (MulAut.conj t).toMonoidHom ∧
      Nat.card D₁=3 ∧ Nat.card D₂=3 ∧ Disjoint D₁ D₂ ∧ D₁ ⊔ D₂=C := by
  let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
  let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
  have hC : IsPGroup 3 C := IsPGroup.of_card (n:=2) hc
  have hi := source_a5_borel_torus_quotient_injective C hCB hC
    (originalA5ProductProjection D e hn ht htn)
    ((originalA5ProductProjection_ker D e hn ht htn).symm ▸ pCore_isPGroup)
  obtain ⟨h₁,h₂,hd,hgen⟩ := Theory.AlternatingFive.nine_torus_coordinate_kernels q hi hC hc
  obtain ⟨hl,hj⟩ := source_original_odd_axes_le_factors D e hn ht htn
    (le_centralizer_iff.mp (source_original_block_commutes_prescribed_conjugate D hb ht htn))
    (source_original_block_core_elementary D hn hb hz) C hCR (by rw [hc]; decide)
  refine ⟨hl,hj,?_,?_,Subgroup.disjoint_map C.subtype_injective hd.symm,?_⟩
  · rw [card_map_of_injective C.subtype_injective]
    exact h₂
  · rw [card_map_of_injective C.subtype_injective]
    exact h₁
  · rw [←Subgroup.map_sup,sup_comm,hgen,←MonoidHom.range_eq_map,range_subtype]
end CFSG.Quasithin.Chapter10
