module
public import CFSG.Quasithin.ChapterG.Section11.Multiplicity

/-!
# Low-rank displacement on the exchanged component constituents

The sum of all component-orbit submodules fixed pointwise by the low-rank
witness is invariant under the original elementary actor. Clifford theory
supplies a complement, preserved by the witness because every constituent
has dimension at least three. Its moved space lies in that complement.
If the fixed sum were nonzero, G.10.10 would put the original marked point
in both complementary subspaces. Thus the witness moves every nonzero
component-orbit submodule.

The two exchanged constituents each contribute positive displacement rank.
The bound of two forces rank one on each and leaves no further summand.
This proves that their sum is the whole original module, without a
proper-full-linear-action premise. It supplies the actual transvection
used by `ExchangedModels`, with the original relative Sylow normality.

Source: Aschbacher--Smith G.10.10, G.10.16(2),(4), and G.11.6,
printed pp.360,363--366. This is the low-rank specialization only.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.ChapterG.Section11

private theorem small_displacement_preserves_subrepresentation
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : IsIrreducible ρ)
    (H : Subgroup G) [H.Normal] (a : G)
    (hsmall : ∀ J : Subrepresentation (ρ.comp H.subtype), IsIrreducible J.toRepresentation →
      finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) < finrank (ZMod 2) J.toSubmodule)
    (R : Subrepresentation (ρ.comp H.subtype)) : R.toSubmodule.map (ρ a) = R.toSubmodule := by
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi H
  let e : Subrepresentation (ρ.comp H.subtype) ≃o
      Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let : IsAtomistic (Subrepresentation (ρ.comp H.subtype)) :=
    e.symm.isAtomistic_of_isAtomistic inferInstance
  let c := conjugateSubrepresentationOrderIso ρ H a
  have hc (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsAtom J) : c J = J := by
    apply Subrepresentation.toSubmodule_injective
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact map_constituent_eq_self_of_displacement_lt ρ H a J
      ((Subrepresentation.irreducible_iff_isAtom J).mpr hJ)
      (hsmall J ((Subrepresentation.irreducible_iff_isAtom J).mpr hJ))
  have hs : c '' {J | IsAtom J ∧ J ≤ R} = {J | IsAtom J ∧ J ≤ R} := by
    ext J
    constructor
    · rintro ⟨Q,hQ,rfl⟩
      rwa [hc Q hQ.1]
    · intro hJ
      exact ⟨J,hJ,hc J hJ.1⟩
  have he : c R = R := calc
    c R = c (sSup {J | IsAtom J ∧ J ≤ R}) := congrArg c (sSup_atoms_le_eq R).symm
    _ = sSup (c '' {J | IsAtom J ∧ J ≤ R}) := by rw [c.map_sSup,sSup_image]
    _ = R := by rw [hs,sSup_atoms_le_eq]
  simpa only [c,conjugateSubrepresentationOrderIso_toSubmodule] using
    congrArg Subrepresentation.toSubmodule he

private theorem displacement_in_subspace
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a : G) (U : Submodule (ZMod 2) V)
    (hu : U.map (ρ a) = U) : U.map (ρ a - LinearMap.id) ≤ U := by
  rintro _ ⟨w,hw,rfl⟩
  exact U.sub_mem (hu ▸ Submodule.mem_map_of_mem hw) hw

private theorem subrepresentation_compl
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (R Q : Subrepresentation ρ) (hc : IsCompl R Q) :
    IsCompl R.toSubmodule Q.toSubmodule := by
  refine ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hc.inf_eq_bot),
    codisjoint_iff.mpr ?_⟩
  rw [← Subrepresentation.toSubmodule_sup,hc.sup_eq_top]
  rfl

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem component_constituents_large
    (h : Section10.Hypothesis ρ B v W X X₀) (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L)
    (J : Subrepresentation (ρ.comp (componentOrbit L ⊤).subtype))
    (hJ : IsIrreducible J.toRepresentation) : 3 ≤ finrank (ZMod 2) J.toSubmodule := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  apply PerfectInvolutionExtension.constituent_dimension ρ (h.irreducible_of_not_solvable hn) H
    ?_ J hJ
  rw [ρ.ker_eq_bot h.faithful]
  exact fun hh => hL.componentOrbit_top_ne_bot (le_bot_iff.mp hh)

/-- The low-rank witness moves every nonzero submodule of the actual component
orbit. The marked-point containment G.10.10 replaces any fixed-space premise. -/
theorem component_subrepresentation_moved
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hS : NormalSylow ρ v X) (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (a : X) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace ρ a)
    (R : Subrepresentation (ρ.comp (componentOrbit L ⊤).subtype)) (hR : R ≠ ⊥) :
    R.toSubmodule.map (ρ a - LinearMap.id) ≠ ⊥ := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  have hsmall (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) < finrank (ZMod 2) J.toSubmodule := by
    have hd := component_constituents_large h hn hL J hJ
    change finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 at hr
    exact lt_of_le_of_lt hr (by omega)
  let δ := ρ a - LinearMap.id
  let F : Subrepresentation (ρ.comp H.subtype) :=
    ⨆ Q : {Q : Subrepresentation (ρ.comp H.subtype) // Q.toSubmodule ≤ δ.ker}, Q.val
  have hFker : F.toSubmodule ≤ δ.ker := by
    dsimp only [F]
    rw [Homogeneous.toSubmodule_iSup]
    exact iSup_le fun Q => Q.property
  have hFX : X ≤ subspaceStabilizer ρ F.toSubmodule := by
    apply le_subspaceStabilizer
    intro x hx w hw
    have hc : conjugateSubrepresentationOrderIso ρ H x F ≤ F := by
      dsimp only [F]
      rw [OrderIso.map_iSup]
      refine iSup_le fun Q => ?_
      let C := conjugateSubrepresentationOrderIso ρ H x Q.val
      have hC : C.toSubmodule ≤ δ.ker := by
        rw [conjugateSubrepresentationOrderIso_toSubmodule]
        rintro _ ⟨u,hu,rfl⟩
        have hfix : ρ a u = u := sub_eq_zero.mp (Q.property hu)
        have hcomm := congrArg (fun g : G => ρ g u)
          (congrArg Subtype.val (mul_comm a (⟨x,hx⟩ : X)))
        simp only [Subgroup.coe_mul,map_mul,Module.End.mul_apply] at hcomm
        change ρ a (ρ x u) - ρ x u = 0
        rw [hcomm,hfix,sub_self]
      exact le_iSup_of_le ⟨C,hC⟩ le_rfl
    apply hc
    change ρ x w ∈ (conjugateSubrepresentationOrderIso ρ H x F).toSubmodule
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact Submodule.mem_map_of_mem hw
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi H
  let e : Subrepresentation (ρ.comp H.subtype) ≃o
      Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let : ComplementedLattice (Subrepresentation (ρ.comp H.subtype)) := e.symm.complementedLattice
  obtain ⟨C,hFC⟩ := exists_isCompl F
  have hFC' := subrepresentation_compl (ρ.comp H.subtype) F C hFC
  have hDC : LinearMap.range δ ≤ C.toSubmodule := by
    rintro _ ⟨w,rfl⟩
    obtain ⟨u,hu,t,ht,rfl⟩ := Submodule.mem_sup.mp
      (show w ∈ F.toSubmodule ⊔ C.toSubmodule by rw [hFC'.sup_eq_top]; trivial)
    rw [map_add,show δ u = 0 from hFker hu,zero_add]
    exact displacement_in_subspace ρ a C.toSubmodule
      (small_displacement_preserves_subrepresentation ρ hi H a hsmall C)
      (Submodule.mem_map_of_mem ht)
  have hFbot : F = ⊥ := by
    by_contra hF
    obtain ⟨S,_,hXS,hnS⟩ := hS
    obtain ⟨c⟩ := cover
    have hvF := h.point_mem_normal_component_subspace hn hL hm S
      ((normal_subgroupOf_iff_le_normalizer hXS).mp hnS)
      (c.component_normalizer_index_le_two hL) F.toSubmodule
      (le_subspaceStabilizer ρ _ (fun g hg u hu => F.apply_mem_toSubmodule ⟨g,hg⟩ hu))
      hFX (fun he => hF (Subrepresentation.toSubmodule_injective he))
    exact h.point_ne_zero (Submodule.disjoint_def.mp hFC'.disjoint v hvF (hDC hv))
  intro hz
  have hRker : R.toSubmodule ≤ δ.ker := by
    intro u hu
    have hh := Submodule.mem_map_of_mem (f := δ) hu
    rw [show R.toSubmodule.map δ = ⊥ from hz] at hh
    exact hh
  have hRF : R ≤ F := le_iSup_of_le ⟨R,hRker⟩ le_rfl
  exact hR (le_bot_iff.mp (hRF.trans_eq hFbot))


omit [Finite G] in
private theorem displacement_rank_sum
    (a : G) (I J : Submodule (ZMod 2) V) (hd : Disjoint I J)
    (hi : I.map (ρ a) = I) (hj : J.map (ρ a) = J) :
    finrank (ZMod 2) ((I ⊔ J).map (ρ a - LinearMap.id)) =
      finrank (ZMod 2) (I.map (ρ a - LinearMap.id)) +
      finrank (ZMod 2) (J.map (ρ a - LinearMap.id)) := by
  have hdis := hd.mono (displacement_in_subspace ρ a I hi) (displacement_in_subspace ρ a J hj)
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (I.map (ρ a - LinearMap.id)) (J.map (ρ a - LinearMap.id))
  rw [hdis.eq_bot,finrank_bot,add_zero,← Submodule.map_sup] at hh
  exact hh

/-- In the exchanged branch the original low-rank witness forces the two
selected summands to fill the whole space and has rank one on each. -/
theorem exchanged_lowRank_pair
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I) :
    ∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x)) ∧
      finrank (ZMod 2) V = 2 * finrank (ZMod 2) I ∧
      ∃ a : X, orderOf (a : G) = 2 ∧ v ∈ RankTwo.movedSpace ρ a ∧
        finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧ I.map (ρ a) = I ∧
        finrank (ZMod 2) (I.map (ρ a - LinearMap.id)) = 1 ∧
        finrank (ZMod 2) ((I.map (ρ x)).map (ρ a - LinearMap.id)) = 1 := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  obtain ⟨x,hx,_,hdis,_⟩ := hgeo
  obtain ⟨a,ha,ha2,_,har,hav⟩ := hw.exists_involution h.point_ne_zero
  let aX : X := ⟨a,ha⟩
  let R := invariantSubspace ρ H I hI.invariant
  let Q := conjugateSubrepresentationOrderIso ρ H x R
  have hR : IsIrreducible R.toRepresentation := hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H
  have hQ : IsIrreducible Q.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom Q).mpr
      (((conjugateSubrepresentationOrderIso ρ H x).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hR))
  have hsmall (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
      finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) < finrank (ZMod 2) J.toSubmodule := by
    have hd := component_constituents_large h hn hL J hJ
    change finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 at har
    exact lt_of_le_of_lt har (by omega)
  have hstable (J : Subrepresentation (ρ.comp H.subtype)) :
      J.toSubmodule.map (ρ a) = J.toSubmodule :=
    small_displacement_preserves_subrepresentation ρ hi H a hsmall J
  have hpos (J : Subrepresentation (ρ.comp H.subtype)) (hJ : J ≠ ⊥) :
      0 < finrank (ZMod 2) (J.toSubmodule.map (ρ a - LinearMap.id)) :=
    Nat.pos_of_ne_zero (fun he => component_subrepresentation_moved h cover hS hn hL hm
      aX har hav J hJ (Submodule.finrank_eq_zero.mp he))
  have hpR := hpos R ((Subrepresentation.irreducible_iff_isAtom R).mp hR).ne_bot
  have hpQ := hpos Q ((Subrepresentation.irreducible_iff_isAtom Q).mp hQ).ne_bot
  have hQspace : Q.toSubmodule = I.map (ρ x) :=
    conjugateSubrepresentationOrderIso_toSubmodule ρ H x R
  have hdisRQ : Disjoint R.toSubmodule Q.toSubmodule := by
    rw [hQspace]
    exact hdis
  have hsum := displacement_rank_sum a R.toSubmodule Q.toSubmodule hdisRQ (hstable R) (hstable Q)
  have hle := Submodule.finrank_mono (show (R.toSubmodule ⊔ Q.toSubmodule).map
      (ρ a - LinearMap.id) ≤ LinearMap.range (ρ a - LinearMap.id) from
    by rintro _ ⟨u,_,rfl⟩; exact ⟨u,rfl⟩)
  have hsumle : finrank (ZMod 2) (R.toSubmodule.map (ρ a - LinearMap.id)) +
      finrank (ZMod 2) (Q.toSubmodule.map (ρ a - LinearMap.id)) ≤ 2 := by
    rw [← hsum]
    exact hle.trans har
  have htwo : finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 := by
    apply le_antisymm har
    exact (show 2 ≤ _ from by omega).trans hle
  have hRone : finrank (ZMod 2) (R.toSubmodule.map (ρ a - LinearMap.id)) = 1 := by
    change finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 at har
    omega
  have hQone : finrank (ZMod 2) (Q.toSubmodule.map (ρ a - LinearMap.id)) = 1 := by
    change finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 at har
    omega
  have htop : R ⊔ Q = ⊤ := by
    let := NormalConstituentDisplacement.restriction_semisimple ρ hi H
    let e : Subrepresentation (ρ.comp H.subtype) ≃o
        Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
      Subrepresentation.subrepresentationSubmoduleOrderIso
    let : ComplementedLattice (Subrepresentation (ρ.comp H.subtype)) := e.symm.complementedLattice
    obtain ⟨C,hC⟩ := exists_isCompl (R ⊔ Q)
    have hC' := subrepresentation_compl (ρ.comp H.subtype) (R ⊔ Q) C hC
    have hs := displacement_rank_sum a (R ⊔ Q).toSubmodule C.toSubmodule
      hC'.disjoint (hstable (R ⊔ Q)) (hstable C)
    rw [hC'.sup_eq_top,Submodule.map_top] at hs
    rw [← Subrepresentation.toSubmodule_sup] at hsum
    by_cases hb : C = ⊥
    · simpa only [hb,sup_bot_eq] using hC.sup_eq_top
    · have hpC := hpos C hb
      have hbound : finrank (ZMod 2) ((R ⊔ Q).toSubmodule.map (ρ a - LinearMap.id)) +
          finrank (ZMod 2) (C.toSubmodule.map (ρ a - LinearMap.id)) ≤ 2 := hs ▸ har
      omega
  have hcompl : IsCompl I (I.map (ρ x)) := by
    refine ⟨hdis,codisjoint_iff.mpr ?_⟩
    rw [← hQspace]
    change R.toSubmodule ⊔ Q.toSubmodule = ⊤
    rw [← Subrepresentation.toSubmodule_sup,htop]
    rfl
  have hdimJ := (Submodule.equivMapOfInjective (ρ x) (ρ.apply_bijective x).injective I).finrank_eq
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hQspace] at hQone
  exact ⟨x,hx,hcompl,by omega,aX,ha2,hav,htwo,hstable R,hRone,hQone⟩

end CFSG.Quasithin.ChapterG.Section11
