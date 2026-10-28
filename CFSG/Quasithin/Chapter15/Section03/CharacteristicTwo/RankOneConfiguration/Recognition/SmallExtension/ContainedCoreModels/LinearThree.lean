module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.Reduction
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# The nonabelian binary linear-three configuration

The two marked matrices have no common fixed vector on the natural center.
Duality therefore makes each dual summand of Q/Z(Q) commutator-generated
under the actual Y₊ image, with the same quotient actor on both summands.
The derived subgroup of Q is a nonzero invariant subgroup of its natural
center: the quotient is abelian, while an abelian Q would have trivial
Q/Z(Q). Transitivity of SL₃(2) on nonzero columns makes [Q,Q] = Z(Q).
Nilpotence now lifts generation to all of Q. The source normalizer and
residual identities give Q ≤ O₂(Y₊), centralization by C_I(Y₊), and the
actual exclusion through SourceData.excluded_of_models.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, and proof of
15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover LinearModels LinearThree
namespace ContainedCoreModels

variable {G : Type*} [Group G] {L : Subgroup G}

private theorem coinvariants_prod_eq_top
    {A V W : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A W)
    (hρ : Coinvariants.ker ρ = ⊤) (hσ : Coinvariants.ker σ = ⊤) :
    Coinvariants.ker (ρ.prod σ) = ⊤ := by
  let U := Coinvariants.ker (ρ.prod σ)
  have h₁ : Coinvariants.ker ρ ≤ U.comap (LinearMap.inl (ZMod 2) V W) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    have hh := Coinvariants.sub_mem_ker (ρ := ρ.prod σ) a (v,0)
    simpa using hh
  have h₂ : Coinvariants.ker σ ≤ U.comap (LinearMap.inr (ZMod 2) V W) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    have hh := Coinvariants.sub_mem_ker (ρ := ρ.prod σ) a (0,w)
    simpa using hh
  apply top_unique
  intro v _
  have hh := U.add_mem (h₁ (hρ ▸ (show v.1 ∈ (⊤ : Submodule (ZMod 2) V) from trivial)))
    (h₂ (hσ ▸ (show v.2 ∈ (⊤ : Submodule (ZMod 2) W) from trivial)))
  simpa using hh

/-- Both dual summands are generated under the original marked Y₊ action. -/
theorem dual_pair_coinvariants [Finite G]
    {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData κ d c) (center : FullCenter c.L natural)
    (plane : MarkedPlane center d.V₂) :
    Coinvariants.ker ((natural.dual.prod natural.dual).comp
      ((d.Yplus.subgroupOf c.L).map center.actor).subtype) = ⊤ := by
  obtain ⟨m⟩ := caseThree center plane s.component_parabolic s.component_residual
  let B := (d.Yplus.subgroupOf c.L).map center.actor
  have hfixed : Representation.OneCohomology.fixed (natural.comp B.subtype) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hm (b : SL) (hb : b ∈ (d.Yplus.subgroupOf c.L).map m.model.actorMap) :
        natural b (natural m.changeOfCoordinates v) = natural m.changeOfCoordinates v := by
      obtain ⟨l,hl,rfl⟩ := hb
      have hlv : natural (center.actor l) v = v := hv ⟨center.actor l, mem_map_of_mem _ hl⟩
      rw [m.actorMap_eq, map_mul, map_mul]
      simp only [Module.End.mul_apply, inv_self_apply, hlv]
    have hz := fixed_marked_matrices_eq_zero (natural m.changeOfCoordinates v)
      (hm _ m.transvection_mem) (hm _ m.rotation_mem)
    exact (natural.apply_bijective m.changeOfCoordinates).injective
      (hz.trans (map_zero _).symm)
  have hgen : Coinvariants.ker (natural.dual.comp B.subtype) = ⊤ :=
    Representation.OneCohomology.commutator_dual_eq_top (natural.comp B.subtype) hfixed
  exact coinvariants_prod_eq_top (natural.dual.comp B.subtype)
    (natural.dual.comp B.subtype) hgen hgen

/-- The actual natural center lies in the derived group, retaining the central layer. -/
theorem natural_center_le_derived
    (c : FullCenter L natural)
    (h : HasSectionModel L (extensionCore L) (coreCenter L) c.actor
      (natural.dual.prod natural.dual)) :
    coreCenter L ≤ ⁅extensionCore L, extensionCore L⁆ := by
  let Q := extensionCore L
  let Z := coreCenter L
  obtain ⟨_, hLQ, _, hn, e, _⟩ := h
  let := hn
  let f : Q →* Multiplicative (Module.Dual (ZMod 2) Space × Module.Dual (ZMod 2) Space) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Q))
  have hder : ⁅Q,Q⁆ ≤ Z := by
    apply commutator_le.mpr
    intro a ha b hb
    have he : f ⁅(⟨a,ha⟩ : Q), ⟨b,hb⟩⁆ = 1 := by
      rw [map_commutatorElement]
      simp [commutatorElement_def]
    have hk : (⁅(⟨a,ha⟩ : Q), (⟨b,hb⟩ : Q)⁆) ∈ Z.subgroupOf Q :=
      (QuotientGroup.eq_one_iff ⁅(⟨a,ha⟩ : Q), (⟨b,hb⟩ : Q)⁆).mp
        (e.injective (he.trans e.map_one.symm))
    exact hk
  have hne : ⁅Q,Q⁆ ≠ ⊥ := by
    intro hb
    have hc := commutator_self_eq_bot_iff.mp hb
    have hQZ : Q ≤ Z := le_inf le_rfl (le_centralizer_iff_isMulCommutative.mpr hc)
    have htop : Z.subgroupOf Q = ⊤ := subgroupOf_eq_top.mpr hQZ
    have hs : Subsingleton (Q ⧸ Z.subgroupOf Q) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have ht := e.symm.injective.subsingleton
    obtain ⟨v,hv⟩ := exists_ne (1 : Multiplicative
      (Module.Dual (ZMod 2) Space × Module.Dual (ZMod 2) Space))
    exact hv (ht.elim _ _)
  have hnorm : L ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
    have hh := hLQ.trans (normalizer_le_normalizer_characteristic_image Q
      ⁅(⊤ : Subgroup Q), ⊤⁆)
    simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hh
  obtain ⟨z,hz,hz1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp ((Subgroup.nontrivial_iff_ne_bot _).mpr hne)
  let zC : coreCenter L := ⟨z,hder hz⟩
  have hz0 : (c.equiv zC).toAdd ≠ 0 := by
    intro hh
    have hh' : c.equiv zC = 1 := congrArg Multiplicative.ofAdd hh
    exact hz1 (congrArg Subtype.val (c.equiv.injective (hh'.trans c.equiv.map_one.symm)))
  intro w hw
  by_cases hw1 : w = 1
  · exact hw1 ▸ one_mem _
  let wC : coreCenter L := ⟨w,hw⟩
  have hw0 : (c.equiv wC).toAdd ≠ 0 := by
    intro hh
    have hh' : c.equiv wC = 1 := congrArg Multiplicative.ofAdd hh
    exact hw1 (congrArg Subtype.val (c.equiv.injective (hh'.trans c.equiv.map_one.symm)))
  obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (c.equiv zC).toAdd (c.equiv wC).toAdd hz0 hw0
  obtain ⟨l,hl⟩ := c.actor_surjective a
  have hc : centerConjugate L l zC = wC := by
    apply c.equiv.injective
    rw [c.action]
    change Multiplicative.ofAdd (natural (c.actor l) (c.equiv zC).toAdd) = c.equiv wC
    rw [hl]
    exact congrArg Multiplicative.ofAdd ha
  have hh := ((mem_normalizer_iff.mp (hnorm l.property)) z).mp hz
  have heq : (l : G) * z * (l : G)⁻¹ = w := congrArg Subtype.val hc
  exact heq ▸ hh


variable [Finite G] {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The full source commutator calculation in C.1.34(3), including its center. -/
theorem linearThree_core_eq_commutator (s : SourceData κ d c)
    (center : FullCenter c.L natural) (plane : MarkedPlane center d.V₂)
    (dual : HasSectionModel c.L (extensionCore c.L) (coreCenter c.L) center.actor
      (natural.dual.prod natural.dual)) :
    extensionCore c.L = ⁅extensionCore c.L, d.Yplus⁆ :=
  core_eq_commutator_of_section s dual (natural_center_le_derived center dual)
    (dual_pair_coinvariants s center plane)

/-- The full nonabelian core lies in the actual two-core of Y₊. -/
theorem linearThree_core_le_yplus_core (s : SourceData κ d c)
    (center : FullCenter c.L natural) (plane : MarkedPlane center d.V₂)
    (dual : HasSectionModel c.L (extensionCore c.L) (coreCenter c.L) center.actor
      (natural.dual.prod natural.dual)) :
    extensionCore c.L ≤ d.Yplus.pCoreIn 2 := by
  rw [linearThree_core_eq_commutator s center plane dual]
  exact core_commutator_le_yplus_core s

/-- The source centralizer D centralizes the whole nonabelian core. -/
theorem linearThree_centralizes_core (s : SourceData κ d c)
    (center : FullCenter c.L natural) (plane : MarkedPlane center d.V₂)
    (dual : HasSectionModel c.L (extensionCore c.L) (coreCenter c.L) center.actor
      (natural.dual.prod natural.dual)) :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
  inf_le_right.trans (centralizer_le
    ((linearThree_core_le_yplus_core s center plane dual).trans (pCoreIn_le 2 d.Yplus)))

/-- Actual exclusion of the third linear configuration, with no extra core premise. -/
theorem linearThree_excluded (s : SourceData κ d c)
    (center : FullCenter c.L natural) (plane : MarkedPlane center d.V₂)
    (dual : HasSectionModel c.L (extensionCore c.L) (coreCenter c.L) center.actor
      (natural.dual.prod natural.dual)) : False :=
  s.excluded_of_models (.linearThree center plane dual)
    (linearThree_centralizes_core s center plane dual)

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
