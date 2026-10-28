module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSize
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.BaumannControl
public import Theory.GroupTheory.PCoreRestriction
public import Theory.SpecificGroups.SL2.OriginalSylowPair
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original module inside the zero-core pair's left parabolic

The original Sylow intersection V = T ∩ L is normalized by D, sourceS
and B ∩ R, so it lies in the two-core Q of the whole left parabolic
DS(B ∩ R). On the moved reduced module U = [W,L], its centralizer is
exactly O₂(L); the literal quotient action has order 2ⁿ.

Two conjugates of V generate L. Accordingly their two displacements on
U generate U. Since U is elementary and has order at least 2^(2n),
each displacement has order at least 2ⁿ. Both U and V lie in Q, giving
|[Q,Q]| ≥ 2ⁿ ≥ 4. In particular the left core is nonabelian, and a core
whose derived subgroup has order at most two is excluded before any
amalgam recognition. No equality of sourceS with T is used.

These are structural inputs to the remaining mixed F.1.12 recognition;
they do not assert its exhaustive catalogue conclusion. The Chapter12
consumer applies them to the same original escaping prime pair.
Source: Aschbacher--Smith 5.2.2, printed pp.647--648, with the constituent
bound E.2.13(4), p.225 (`refs/quasithin.pdf`), and generation of SL₂ by
opposed defining-characteristic Sylow subgroups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The action kernel on the original moved module, inside the original
Sylow intersection, is precisely the embedded two-core of L. -/
theorem Input.moved_sylow_centralizer
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ((T : Subgroup G) ⊓ L) ⊓ centralizer ((⁅W,L⁆ : Subgroup G) : Set G) = L.pCoreIn 2 := by
  have hc := h.commutator_input.sylow_centralizer_eq_core
  have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer h.sylow_normalizes)
  apply le_antisymm
  · apply le_trans _ (inf_pCoreIn_le_of_le 2 (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))
    exact le_inf (inf_le_left.trans inf_le_right)
      ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans_eq hc)
  · rw [←hc] at hcore
    exact le_inf (le_inf (hcore.trans inf_le_left) (pCoreIn_le 2 L))
      (hcore.trans inf_le_right)

/-- The actual Sylow quotient acting on [W,L] has order 2ⁿ, at the
original left degree and with the full intrinsic kernel retained. -/
theorem Input.moved_sylow_action_index
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    (L.pCoreIn 2).relIndex ((T : Subgroup G) ⊓ L) = 2^n := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  let q := QuotientGroup.mk' (pCore 2 L)
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : Nat.card Q = 2^n := by
    calc
      Nat.card Q = Nat.card Q' := Nat.card_congr
        ((Q : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card F := (Nat.card_congr
        (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive Q').symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd)
      _ = 2^n := hF
  have hpmap : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hP,subgroupOf_map_subtype]
  rw [←hpmap, pCoreIn,relIndex_map_map_of_injective _ _ L.subtype_injective]
  have hi := relIndex_ker (P : Subgroup L) q
  have hi' : (pCore 2 L).relIndex (P : Subgroup L) = Nat.card Q := by
    simpa only [q,QuotientGroup.ker_mk', Q, Sylow.coe_mapSurjective] using hi
  exact hi'.trans hQ

omit [Finite G] in
private theorem commutator_join_of_normalizes {U X Y : Subgroup G}
    (hx : X ≤ normalizer (U : Set G)) (hy : Y ≤ normalizer (U : Set G)) :
    ⁅U,X ⊔ Y⁆ = ⁅U,X⁆ ⊔ ⁅U,Y⁆ := by
  let C := ⁅U,X⁆ ⊔ ⁅U,Y⁆
  have hCU : C ≤ U := sup_le
    (le_normalizer_iff_commutator_le_left.mp hx)
    (le_normalizer_iff_commutator_le_left.mp hy)
  have hn : X ⊔ Y ≤ normalizer (C : Set G) := by
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      exact (commutator_mono le_rfl hCU).trans
        ((commutator_comm X U).le.trans le_sup_left)
    · apply le_normalizer_iff_commutator_le_right.mpr
      exact (commutator_mono le_rfl hCU).trans
        ((commutator_comm Y U).le.trans le_sup_right)
  apply le_antisymm
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (X ⊔ Y) X Y U C hn le_sup_left le_sup_right
      ((commutator_comm X U).le.trans le_sup_left)
      ((commutator_comm Y U).le.trans le_sup_right)
  · exact sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)

/-- Opposed Sylow generation bounds the displacement on the original
moved module without choosing a natural or symmetric-five model. -/
theorem Input.moved_sylow_displacement_bound
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    2^n ≤ Nat.card (⁅⁅W,L⁆,(T : Subgroup G) ⊓ L⁆ : Subgroup G) := by
  let U := ⁅W,L⁆
  let V := (T : Subgroup G) ⊓ L
  have hu := h.moved_reduced_size
  let : IsElementaryAbelian 2 U := hu.1
  have hn : L ≤ normalizer (U : Set G) := normalizer_commutator_ge_right W L
  have hm : ⁅U,L⁆ = U := commutator_isPPerfect_idempotent L W
    h.local_mem.2.2.1 (by let := h.reduced.2.1; exact IsElementaryAbelian.isPGroup 2 W)
    (le_sup_left.trans (reduced_normalizes h.reduced))
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    change a (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨g,_,hgen,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair q hq hk P
  let f := (MulAut.conj (g : G)).toMonoidHom
  have hpmap : (P : Subgroup L).map L.subtype = V := by
    rw [hP,subgroupOf_map_subtype]
  have hgen' : V ⊔ V.map f = L := by
    have hh := congrArg (map L.subtype) hgen
    rw [Subgroup.map_sup,map_map,←MonoidHom.range_eq_map,range_subtype,hpmap] at hh
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom = f.comp L.subtype := by ext x; rfl
    rwa [he,←map_map,hpmap] at hh
  have huconj : U.map f = U := mem_normalizer_iff_map_conj_eq.mp (hn g.property)
  have hVgL : V.map f ≤ L := by rw [←hgen']; exact le_sup_right
  have hdecomp : U = ⁅U,V⁆ ⊔ (⁅U,V⁆).map f := by
    rw [map_commutator,huconj,←commutator_join_of_normalizes (inf_le_right.trans hn)
      (hVgL.trans hn),hgen',hm]
  let C := ⁅U,V⁆
  have hCU : C ≤ U := le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hn)
  have hCgU : C.map f ≤ U := (map_mono hCU).trans huconj.le
  have hc : C.map f ≤ normalizer (C : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact hCgU.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hCU))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C (C.map f) hc
  rw [card_map_of_injective (MulAut.conj (g : G)).injective,←hdecomp] at hprod
  have hpos : 1 ≤ Nat.card (C ⊓ C.map f : Subgroup G) := Nat.card_pos
  have hupp : Nat.card U ≤ Nat.card C ^ 2 := by nlinarith
  have hl : (2^n)^2 ≤ Nat.card C ^ 2 := by
    rw [←pow_mul]
    simpa only [Nat.mul_comm n 2] using hu.2.2.trans hupp
  change 2^n ≤ Nat.card C
  nlinarith

namespace Prime

/-- The entire original Sylow intersection lies in the two-core of
DS(B ∩ R), using normalization by each of the three literal factors. -/
theorem LocalData.original_sylow_le_left_parabolic_core
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (T : Subgroup G) ⊓ L ≤
      ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 := by
  let S := Global.sourceS L H
  let U := (T : Subgroup G) ⊓ L
  have hUS : U ≤ S := by
    change (T : Subgroup G) ⊓ L ≤ Global.sourceS L H
    rw [←d.S_intersection_left]
    exact inf_le_left
  have hSN : S ≤ normalizer (U : Set G) :=
    (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf)
  have hBN : B ≤ normalizer (U : Set G) := by
    change B ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
    rw [←d.S_intersection_left]
    exact (le_inf (c.right_le.trans (Global.intersection_normalizes_sourceS L H))
      (c.right_le.trans inf_le_left)).trans inf_normalizer_le_normalizer_inf
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (hUS.trans (le_sup_right.trans le_sup_left))
    (sup_le (sup_le (hd.le_cartan.trans (c.left_le.trans inf_le_right)) hSN)
      (inf_le_left.trans hBN))

/-- The derived subgroup of the whole left core contains the original
Sylow displacement, so it has order at least 2ⁿ. -/
theorem LocalData.left_parabolic_core_derived_bound
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    let Q := ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2
    2^n ≤ Nat.card (⁅Q,Q⁆ : Subgroup G) := by
  have hv := d.original_sylow_le_left_parabolic_core h hH c hd
  exact h.moved_sylow_displacement_bound.trans
    (card_le_of_le (commutator_mono (h.moved_reduced_size.2.1.trans hv) hv))

/-- An abelian left core would kill the faithful original Sylow action. -/
theorem LocalData.left_parabolic_core_not_commutative
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ¬ IsMulCommutative (((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) := by
  intro ha
  let Q := ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2
  let : IsMulCommutative Q := ha
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hu := d.original_sylow_le_left_parabolic_core h hH c hd
  have hm := h.moved_reduced_size.2.1
  have hc : (T : Subgroup G) ⊓ L ≤ centralizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
    intro x hx y hy
    exact congrArg Q.subtype (mul_comm (⟨y,hu (hm hy)⟩ : Q) ⟨x,hu hx⟩)
  have hk : (T : Subgroup G) ⊓ L ≤ L.pCoreIn 2 := by
    rw [←h.moved_sylow_centralizer]
    exact le_inf le_rfl hc
  have hi := h.moved_sylow_action_index
  rw [relIndex_eq_one.mpr hk] at hi
  have hn : 2^2 ≤ (2:ℕ)^n := Nat.pow_le_pow_right (by decide) h.exponent
  omega

end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
