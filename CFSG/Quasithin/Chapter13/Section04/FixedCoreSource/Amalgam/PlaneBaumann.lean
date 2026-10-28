module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneAlpha
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ReplacementConjugates

/-!
# The original plane Baumann decomposition and centralizer kernel

The actual plane marking identifies the Thompson and Baumann images with
the full transposition cube and proves that the six-letter action is onto.
Two opposite cubes generate the quotient, with fixed codimensions two and
two on the original five-space. The enlarged elementary module alpha(T)V,
constructed in PlaneAlpha, therefore satisfies the dimension argument.

This gives the literal alpha decomposition, O2(L) containment in Baum(T),
and saturation of the centralizer of V in L Baum(T). The two-residual of
LT is identified with the actual original component L before transporting
these equalities to G. The selected linear pair supplies Thompson escape;
no enlarged-module, generator, dimension or kernel-saturation premise is
left to its caller. Near-maximum containment is the current branch premise.

The subsequent MS-pair/block conclusion of13.2.2(10), the remaining model
exclusions and the universal13.4.7 source interfaces remain separate steps.
Source: Aschbacher--Smith13.2.2(10), p.878, C.1.37, pp.142--143,
and13.4.7(4), pp.902--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V B : Subgroup G}

/-- The original plane gives simultaneous full Thompson and Baumann images,
retaining the literal kernel and actual augmentation coordinates. -/
theorem exists_original_plane_full_baumann_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let X := L ⊔ (T : Subgroup G)
    ∃ q : X →* Equiv.Perm (Fin 6), ∃ e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)),
      (∀ (x : X) (v : V),
        (e (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd) ∧
      q.ker = pCore 2 X ∧ q.ker = centralizer (V.subgroupOf X : Set X) ∧
      Function.Surjective q ∧
      ((B.pCoreIn 2).subgroupOf X).map q ≤ ChapterB.Offenders.D 6 ∧
      ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf X).map q = ChapterB.Offenders.D 6 ∧
      ((ChapterB.baumann (T : Subgroup G)).subgroupOf X).map q = ChapterB.Offenders.D 6 := by
  obtain ⟨q,e,he,hk,hker,hY,hT,hQ⟩ :=
    exists_original_plane_action_coordinates h structural D m eL W hW hTW
  rw [←hB] at hQ
  let X := L ⊔ (T : Subgroup G)
  let S : Sylow 2 X := T.subtype le_sup_right
  let U := V.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes (((structural G T L h).2.2 V D).1))
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let eu := subgroupOfEquivOfLe hVX
  let ei := eu.trans e
  have hei (x : X) (v : U) : (ei (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (ei v).toAdd := he x (eu v)
  have hUS : U ≤ (S : Subgroup X) := comap_mono D.le_sylow
  have hu : Nat.card U = 32 := (Nat.card_congr eu.toEquiv).trans m.card_module
  have hr : 1 < ChapterB.twoRank (S : Subgroup X) := by
    have hb := elementary_card_le_maxOrder (S : Subgroup X) U hUS inferInstance
    rw [hu,ChapterB.maxOrder_eq_two_pow_rank] at hb
    by_contra! hn
    have hh : 2 ^ ChapterB.twoRank (S : Subgroup X) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by decide) hn
    omega
  have hs : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)
  have hjm : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hs]
  have hj1 : (ChapterB.thompsonJ (S : Subgroup X) 1).map X.subtype =
      ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective X.subtype X.subtype_injective,hs]
  have hjq : (ChapterB.thompsonJ (S : Subgroup X) 1).map q ≤ ChapterB.Offenders.D 6 := by
    apply (map_mono (show ChapterB.thompsonJ (S : Subgroup X) 1 ≤
        (B.pCoreIn 2).subgroupOf X from ?_)).trans hQ
    intro x hx
    exact hJ (hj1 ▸ mem_map_of_mem X.subtype hx)
  have hneq : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≠ ⊥ := by
    intro hh
    have hh := (Subgroup.map_eq_bot_iff _).mp hh
    rw [hk] at hh
    exact hne (hjm ▸ map_mono (f := X.subtype) hh)
  have him := ChapterB.Offenders.SixCorePlane.thompson_image U q ei hei S hUS hk hY hT hr hjq hneq
  have honto := ChapterB.Offenders.SixCorePlane.onto_of_thompson_image q hY (S : Subgroup X) him
  have hb : (ChapterB.baumann (S : Subgroup X)).map X.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change (((S : Subgroup X) ⊓ centralizer (omegaOneCenterAmbient
      (elementaryAbelianMaxJ (S : Subgroup X)) : Set X)).map X.subtype) = _
    rw [baumann_map_injective X.subtype X.subtype_injective,hs]
    rfl
  have himB := ChapterB.Offenders.SixCorePlane.baumann_image U q ei hei S hUS
    (hT.le.trans inf_le_left) him
  have hjback : (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf X =
      elementaryAbelianMaxJ (S : Subgroup X) := by
    rw [←hjm,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective]
  have hbback : (ChapterB.baumann (T : Subgroup G)).subgroupOf X =
      ChapterB.baumann (S : Subgroup X) := by
    rw [←hb,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective]
  exact ⟨q,e,he,hk,hker,honto,hQ,hjback.symm ▸ him,hbback.symm ▸ himB⟩

/-- The full marking with the explicit plane-radical image bound forgotten. -/
theorem exists_original_plane_baumann_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let X := L ⊔ (T : Subgroup G)
    ∃ q : X →* Equiv.Perm (Fin 6), ∃ e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)),
      (∀ (x : X) (v : V),
        (e (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd) ∧
      q.ker = pCore 2 X ∧ q.ker = centralizer (V.subgroupOf X : Set X) ∧
      Function.Surjective q ∧
      ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf X).map q = ChapterB.Offenders.D 6 ∧
      ((ChapterB.baumann (T : Subgroup G)).subgroupOf X).map q = ChapterB.Offenders.D 6 := by
  obtain ⟨q,e,he,hk,hc,ho,_,hj,hb⟩ :=
    exists_original_plane_full_baumann_marking h structural D m eL W hW hTW hB hJ hne
  exact ⟨q,e,he,hk,hc,ho,hj,hb⟩

/-- The original ordinary plane has the source alpha decomposition and full
Baumann centralizer saturation, under its near-maximum containment. -/
theorem original_plane_baumann_of_thompson_one_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    L.pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
      ChapterB.baumann (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ ChapterB.baumann (T : Subgroup G)) ⊓ centralizer (V : Set G) := by
  obtain ⟨hel,hnorm,_⟩ := original_plane_alpha_normalized_of_thompson_one_bound
    h structural D m eL W hW hTW hB hJ hne
  obtain ⟨q,e,he,hk,hker,honto,hj0,_⟩ :=
    exists_original_plane_baumann_marking h structural D m eL W hW hTW hB hJ hne
  let X := L ⊔ (T : Subgroup G)
  let S : Sylow 2 X := T.subtype le_sup_right
  let U := V.subgroupOf X
  let Li := L.subgroupOf X
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes (((structural G T L h).2.2 V D).1))
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let eu := subgroupOfEquivOfLe hVX
  let ei := eu.trans e
  have hei (x : X) (v : U) : (ei (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (ei v).toAdd := he x (eu v)
  have hUS : U ≤ (S : Subgroup X) := comap_mono D.le_sylow
  have hs : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)
  have hjm : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hs]
  have him : (elementaryAbelianMaxJ (S : Subgroup X)).map q = ChapterB.Offenders.D 6 := by
    have hjback : (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf X =
        elementaryAbelianMaxJ (S : Subgroup X) := by
      rw [←hjm,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective]
    change ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf X).map q = _ at hj0
    rwa [hjback] at hj0
  have hdim := ChapterB.Offenders.SixCorePlane.fixed_codimensions U q ei hei honto (S : Subgroup X) him
  obtain ⟨g,hg⟩ := honto ChapterB.Offenders.SixCorePlane.opposite
  have hgen : (elementaryAbelianMaxJ (S : Subgroup X)).map q ⊔
      ((elementaryAbelianMaxJ (S : Subgroup X)).map (MulAut.conj g).toMonoidHom).map q = ⊤ := by
    have hconj : ((elementaryAbelianMaxJ (S : Subgroup X)).map
        (MulAut.conj g).toMonoidHom).map q =
        ((elementaryAbelianMaxJ (S : Subgroup X)).map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp
    rw [hconj,him,hg]
    exact ChapterB.Offenders.SixCorePlane.cube_generation
  have ha : (ChapterB.thompsonAlpha (S : Subgroup X)).map X.subtype =
      ChapterB.thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup X))).map X.subtype = _
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,hjm]
    rfl
  have hb : (ChapterB.baumann (S : Subgroup X)).map X.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change (((S : Subgroup X) ⊓ centralizer (omegaOneCenterAmbient
      (elementaryAbelianMaxJ (S : Subgroup X)) : Set X)).map X.subtype) = _
    rw [baumann_map_injective X.subtype X.subtype_injective,hs]
    rfl
  let E := ChapterB.thompsonAlpha (S : Subgroup X) ⊔ U
  have hEm : E.map X.subtype = ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V := by
    rw [Subgroup.map_sup,ha,map_subgroupOf_eq_of_le hVX]
  have hEi : E = (ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V).subgroupOf X := by
    rw [←hEm,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective]
  let : IsElementaryAbelian 2 E := by
    rw [hEi]
    let := hel
    exact IsElementaryAbelian.comap_of_injective X.subtype X.subtype_injective _
  let : E.Normal := by
    rw [hEi]
    exact normal_subgroupOf_of_le_normalizer hnorm
  have hc : centralizer (U : Set X) = pCore 2 X := hker.symm.trans hk
  obtain ⟨hcore,hdec,hsat⟩ := ChapterB.BaumannArgument.two_conjugate_baumann_of_enlarged_module
    (S : Subgroup X) (pCore_isPGroup.le_sylow_of_normal S) U hUS hc
    (show (⊤ : Subgroup X) ≤ normalizer (E : Set X) from le_normalizer_of_normal)
    q hk g hgen (by rw [hdim.1,hdim.2])
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect Li := hcmp.perfect
  have hpL : IsPPerfect 2 Li := by
    intro N hn hquot
    let : N.Normal := hn
    by_contra hn1
    let : Nontrivial (Li ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn1
    let : Group.IsPerfect (Li ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (Li ⧸ N) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Li ⧸ N) inferInstance
  have hprod : Li ⊔ (S : Subgroup X) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hLX (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  have hres : pResidual 2 X = Li := pResidual_eq_of_isPPerfect_sup Li (S : Subgroup X) hpL S.isPGroup' hprod
  rw [hres] at hcore hdec hsat
  have hLm : Li.map X.subtype = L := map_subgroupOf_eq_of_le hLX
  have hUm : U.map X.subtype = V := map_subgroupOf_eq_of_le hVX
  refine ⟨?_,?_,?_⟩
  · have hh := map_mono (f := X.subtype) hcore
    change (Li.pCoreIn 2).map X.subtype ≤ _ at hh
    rwa [map_pCoreIn_of_injective 2 Li X.subtype X.subtype_injective,hLm,hb] at hh
  · have hh := congrArg (map X.subtype) hdec
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,ha,hLm,hUm,hjm] at hh
    exact hh
  · have hh := congrArg (map X.subtype) hsat
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      Subgroup.map_sup,hb,hLm,hUm] at hh
    exact hh
open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource

/-- The selected original linear pair supplies Thompson escape, so the
source plane decomposition and saturation need no additional escape premise. -/
theorem original_linear_pair_plane_baumann
    {A : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    L.pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
      ChapterB.baumann (T : Subgroup G) ⊓ centralizer (V : Set G) =
        (L ⊔ ChapterB.baumann (T : Subgroup G)) ⊓ centralizer (V : Set G) := by
  have hn := original_pair_linear_thompson_normal h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  exact original_plane_baumann_of_thompson_one_bound h structural D m eL W hW hTW hB hJ
    (thompson_not_le_original_core_of_outside_normalizer h D hout hn)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
