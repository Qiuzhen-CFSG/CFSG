module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Sections
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Original-section calculations for the local part of 14.7.70

All tildes are images under the original U → U/V₁ coordinate homomorphism.
The kernel is the original natural projection's kernel, and the actor is the
original H → H/O₂(H) → S₅. The two-dimensional involution displacement cannot
fix a subspace of codimension at most one, so the earlier F.9.13(6) bound
identifies the nontrivial D-commutator with Zα. The same displacement
argument on the reciprocal Uα/Zα section then places V₁ in the commutator.
Hypothesis symmetry in 14.7.39 does not assert an ambient element swapping
both endpoints.

For rank(U₀) ≤ 2, two invariant binary planes inside a space of dimension at
most three have a nonzero intersection. If distinct, this is a binary line
and is fixed pointwise. Applying `original_complement_fixed_finrank` to both
literal complements and the same p proves their common fixed line; the
original flag identifies it with V₂/V₁. Saturation through the actual V₁
kernel gives Zα ≤ V₂. Abelianness of Uα gives the upper intersection bound;
the marked-cover spanning computation and L-conjugacy give all three
intersection equalities.

The source's permitted rechoice and marked-cover spanning computation remain
separate obligations. In particular `hF`, `hspan`, and `hchoice` in the
conditional consumers are intermediate conclusions to be constructed, not
new earlier-source hypotheses. This module does not assert 14.7.70.

Earlier inputs: 14.5.15(4) supplies ActionDescent (qt-14-05); 14.7.2(1)
supplies ModuleSeparation (qt-14-07-solvable); 14.7.64–65 supply the original
upper-space marking. F.9.13 and the symmetry of 14.7.39 are retained literally,
as are the rank-selection codimension bound and actual original upper actor.
Their earlier-source assembly belongs to qt-14-07. The preceding 14.7.68–69
producers remain qt-14-07-critical-residual-fusion and
qt-14-07-critical-order-two.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.64–65, pp.1069–1070; proof of 14.7.70, pp.1073–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal commutator in the source, distinguished from the flag F. -/
def Fcomm (c : CriticalPath (L := L) F) : Subgroup G := ⁅F.U, c.Uα⁆

/-- Every tilde uses the same original U/V₁ coordinates. -/
abbrev tilde (d : Data T L V F W) (A : Subgroup G) : Submodule (ZMod 2) W :=
  d.conjugationSection.imageSpace A

/-- The original Sylow, as a subgroup of the actual actor H. -/
abbrev actorT : Subgroup F.H := (T : Subgroup G).subgroupOf F.H

/-- The original action's T-fixed space. -/
abbrev fixedT (d : Data T L V F W) : Submodule (ZMod 2) W :=
  Representation.invariants (d.action.comp (actorT (F := F)).subtype)

variable (d : Data T L V F W)

include d in
theorem finite_original : Finite W :=
  Finite.of_surjective (fun x : F.U => (d.conjugationSection.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp d.conjugationSection.onto)

theorem tilde_le_iff {A B : Subgroup G} (hAU : A ≤ F.U) (_hBU : B ≤ F.U)
    (hpoint : F.Vi 1 ≤ B) : tilde d A ≤ tilde d B ↔ A ≤ B := by
  constructor
  · intro h
    have hm : (A.subgroupOf F.U).map d.conjugationSection.coordinates ≤
        (B.subgroupOf F.U).map d.conjugationSection.coordinates := h
    rw [Subgroup.map_le_map_iff, d.conjugationSection.kernel_eq,
      sup_eq_left.mpr (subgroupOf_mono F.U hpoint)] at hm
    intro a ha
    exact hm (show (⟨a, hAU ha⟩ : F.U) ∈ A.subgroupOf F.U from ha)
  · exact d.conjugationSection.imageSpace_mono

theorem tilde_sup {A B : Subgroup G} (hAU : A ≤ F.U) (hBU : B ≤ F.U) :
    tilde d (A ⊔ B) = tilde d A ⊔ tilde d B := by
  let f : Subgroup (Multiplicative W) ≃o Submodule (ZMod 2) W :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change f (((A ⊔ B).subgroupOf F.U).map _) = f _ ⊔ f _
  rw [subgroupOf_sup hAU hBU, Subgroup.map_sup, f.map_sup]

theorem tilde_U₀ : tilde d d.U₀ = d.projection.toLinearMap.ker := by
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    exact (d.mem_U₀ a).mp ha
  · intro hw
    obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
    exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
      ⟨a, (d.mem_U₀ a).mpr (by rw [ha]; exact hw), congrArg Multiplicative.toAdd ha⟩

theorem tilde_card (A : Subgroup G) (hAU : A ≤ F.U) :
    Nat.card (tilde d A) = (F.Vi 1).relIndex A := by
  change Nat.card ((A.subgroupOf F.U).map d.conjugationSection.coordinates) = _
  rw [← relIndex_ker, d.conjugationSection.kernel_eq]
  exact relIndex_subgroupOf hAU

theorem card_eq_tilde_mul (A : Subgroup G) (hAU : A ≤ F.U) (hpoint : F.Vi 1 ≤ A) :
    Nat.card A = Nat.card (tilde d A) * 2 := by
  have hc := card_eq_card_quotient_mul_card_subgroup ((F.Vi 1).subgroupOf A)
  rw [Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv,
    F.card 1 (by decide)] at hc
  rw [(tilde_card d) A hAU]
  exact hc

theorem plane_tilde_finrank : Module.finrank (ZMod 2) (tilde d (F.Vi 2)) = 1 := by
  let := (finite_original d)
  have hc := (card_eq_tilde_mul d) (F.Vi 2) ((F.le_seed 2).trans (Data.V_le_U F))
    (F.monotone (by decide : 1 ≤ 2))
  rw [F.card 2 (by decide)] at hc
  have hc' : Nat.card (tilde d (F.Vi 2)) = 2 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc'
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc'.trans (by decide : 2 = 2 ^ 1))

theorem seed_tilde_finrank : Module.finrank (ZMod 2) (tilde d V) = 2 := by
  let := (finite_original d)
  have hc := (card_eq_tilde_mul d) V (Data.V_le_U F) (F.le_seed 1)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hv] at hc
  have hc' : Nat.card (tilde d V) = 4 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc'
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc'.trans (by decide : 4 = 2 ^ 2))

theorem tilde_invariant {A : Subgroup G}
    (hn : (T : Subgroup G) ≤ normalizer (A : Set G))
    (t : actorT (F := F)) (w : W) (hw : w ∈ tilde d A) :
    d.action t w ∈ tilde d A := by
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  let b : F.U := ⟨(t : F.H) * a * ((t : F.H) : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized (t : F.H).property) a).mp a.property⟩
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
    ⟨b, (mem_normalizer_iff.mp (hn t.property) a).mp ha, d.conjugationSection.equivariant t a⟩

theorem plane_tilde_fixed : tilde d (F.Vi 2) ≤ fixedT d := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  intro t
  exact flag_plane_fixed d.action d.conjugationSection
    ((F.le_seed 2).trans (Data.V_le_U F)) (F.monotone (by decide : 1 ≤ 2))
    (by simpa using F.card 1 (by decide)) (by simpa using F.card 2 (by decide))
    t (F.invariant 2 t.property) a ha

theorem kernel_finrank_le_one (hrank : primeRank 2 d.U₀ ≤ 2) :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1 := by
  let := (finite_original d)
  let := d.U₀_elementary
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup d.U₀) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 d.U₀) x.val) }
  have hc := (primeRank_le_iff_elementary_card_le d.U₀).mp hrank ⊤ ht
  rw [Nat.card_congr (Subgroup.topEquiv).toEquiv] at hc
  rw [d.U₀_card] at hc
  have hk : Nat.card d.projection.toLinearMap.ker ≤ 2 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hk
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hk

private theorem fixed_of_binary_line {Γ X : Type*} [Group Γ] [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X] (ρ : Representation (ZMod 2) Γ X)
    (A : Submodule (ZMod 2) X) (hdim : Module.finrank (ZMod 2) A = 1)
    (hn : ∀ g x, x ∈ A → ρ g x ∈ A) : A ≤ Representation.invariants ρ := by
  have hc : Nat.card A = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    decide
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (0 : A)).mp hc
  intro x hx g
  by_cases hx0 : x = 0
  · simp [hx0]
  have hg0 : ρ g x ≠ 0 := by
    intro h
    apply hx0
    simpa only [ρ.inv_self_apply, map_zero] using congrArg (ρ g⁻¹) h
  exact congrArg Subtype.val
    ((ha ⟨ρ g x, hn g x hx⟩ (fun h => hg0 (congrArg Subtype.val h))).trans
      (ha ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h))).symm)

theorem kernel_fixed_of_rank_le_two (hrank : primeRank 2 d.U₀ ≤ 2) :
    d.projection.toLinearMap.ker ≤ fixedT d := by
  let := (finite_original d)
  have hk := (kernel_finrank_le_one d) hrank
  by_cases hz : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 0
  · have hb := Submodule.finrank_eq_zero.mp hz
    rw [hb]
    exact bot_le
  · apply fixed_of_binary_line (d.action.comp (actorT (F := F)).subtype)
      d.projection.toLinearMap.ker (by omega)
    intro t w hw
    exact d.projection_ker_invariant t w hw

/-- The careful source rechoice fixes Zα/V₁ because it places Zα in V₂U₀;
no fixed-line equality is assumed. -/
theorem selected_point_fixed (c : CriticalPath (L := L) F)
    (hrank : primeRank 2 d.U₀ ≤ 2) (hZU : c.Zα ≤ F.Vi 2 ⊔ d.U₀) :
    tilde d c.Zα ≤ fixedT d := by
  apply (d.conjugationSection.imageSpace_mono hZU).trans
  change tilde d (F.Vi 2 ⊔ d.U₀) ≤ fixedT d
  rw [(tilde_sup d) ((F.le_seed 2).trans (Data.V_le_U F)) d.U₀_le_U, (tilde_U₀ d)]
  exact sup_le (plane_tilde_fixed d) ((kernel_fixed_of_rank_le_two d) hrank)

/-- Two invariant binary planes in a space of dimension at most three have
a common fixed line if each fixed space has dimension one. -/
private theorem common_fixed_line {Γ X : Type*} [Group Γ] [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X] (ρ : Representation (ZMod 2) Γ X)
    (A B K : Submodule (ZMod 2) X)
    (ha : Module.finrank (ZMod 2) A = 2) (hb : Module.finrank (ZMod 2) B = 2)
    (hk : Module.finrank (ZMod 2) K ≤ 1)
    (hab : A ≤ B ⊔ K)
    (hna : ∀ g x, x ∈ A → ρ g x ∈ A)
    (hnb : ∀ g x, x ∈ B → ρ g x ∈ B)
    (hfa : Module.finrank (ZMod 2) ↥(A ⊓ Representation.invariants ρ) = 1)
    (hfb : Module.finrank (ZMod 2) ↥(B ⊓ Representation.invariants ρ) = 1) :
    A ⊓ Representation.invariants ρ = B ⊓ Representation.invariants ρ := by
  by_cases he : A = B
  · rw [he]
  have hsum : Module.finrank (ZMod 2) ↥(A ⊔ B) ≤ 3 := by
    have hm := Submodule.finrank_mono (sup_le hab (le_sup_left : B ≤ B ⊔ K))
    have heq := B.finrank_sup_add_finrank_inf_eq K
    omega
  have hinf : Module.finrank (ZMod 2) ↥(A ⊓ B) = 1 := by
    have heq := A.finrank_sup_add_finrank_inf_eq B
    have hle := Submodule.finrank_mono (inf_le_left : A ⊓ B ≤ A)
    have hn : Module.finrank (ZMod 2) ↥(A ⊓ B) ≠ 2 := by
      intro h2
      have hIA := Submodule.eq_of_le_of_finrank_eq (inf_le_left : A ⊓ B ≤ A) (h2.trans ha.symm)
      have hIB := Submodule.eq_of_le_of_finrank_eq (inf_le_right : A ⊓ B ≤ B) (h2.trans hb.symm)
      exact he (hIA.symm.trans hIB)
    omega
  have hfix : A ⊓ B ≤ Representation.invariants ρ :=
    fixed_of_binary_line ρ (A ⊓ B) hinf (fun g x hx => ⟨hna g x hx.1, hnb g x hx.2⟩)
  have hA := Submodule.eq_of_le_of_finrank_eq
    (le_inf inf_le_left hfix : A ⊓ B ≤ A ⊓ Representation.invariants ρ) (hinf.trans hfa.symm)
  have hB := Submodule.eq_of_le_of_finrank_eq
    (le_inf inf_le_right hfix : A ⊓ B ≤ B ⊓ Representation.invariants ρ) (hinf.trans hfb.symm)
  exact hA.symm.trans hB


/-- Separation in 14.7.2(1) makes the actual V-tilde disjoint from ker p. -/
theorem seed_disjoint_kernel (separation : d.ModuleSeparation) :
    Disjoint (tilde d V) d.projection.toLinearMap.ker := by
  apply Submodule.disjoint_def.mpr
  intro w hw hk
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  exact congrArg Multiplicative.toAdd ((d.conjugationSection.coordinates_eq_one_iff a).mpr
    ((d.seed_projection_zero_iff separation a ha).mp hk))

/-- The literal involution displacement has two binary dimensions. -/
theorem displacement_finrank (s : d.ActionDescent) (h : F.H)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2 := by
  let := finite_original d
  rw [← s.original h, hh]
  exact original_section_upper_displacement_finrank d.naturalQuotient s.projection
    d.projection_onto s.kernel_fixed s.indecomposable t ht

/-- The rank-selection codimension bound and the actual two-dimensional
involution displacement force the nontrivial D-commutator on p.1073. -/
theorem D_commutator_ne_bot (c : CriticalPath (L := L) F)
    (s : d.ActionDescent) (h : F.H) (hmem : (h : G) ∈ c.Uα)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hcodim : Module.finrank (ZMod 2) (tilde d (F.U ⊓ c.Qα)) + 1 ≥
      Module.finrank (ZMod 2) W) : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≠ ⊥ := by
  let := finite_original d
  intro hc
  have hbound : ⁅c.Uα, F.U ⊓ c.Qα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm, hc]
    exact bot_le
  have hfix := d.conjugationSection.fixed_on_imageSpace_of_commutator_le
    c.Uα (F.U ⊓ c.Qα) hbound h hmem
  have hle : tilde d (F.U ⊓ c.Qα) ≤ (d.action h - LinearMap.id).ker := by
    intro w hw
    exact sub_eq_zero.mpr (hfix w hw)
  have hr := (d.action h - LinearMap.id).finrank_range_add_finrank_ker
  rw [displacement_finrank d s h t ht hh] at hr
  have hm := Submodule.finrank_mono hle
  omega

/-- F.9.13(6)'s small commutator bound now identifies the nontrivial group;
this proves the containment of Zα in the actual Fcomm. -/
theorem D_commutator_eq_Zα (c : CriticalPath (L := L) F)
    (hne : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≠ ⊥)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ⁅F.U ⊓ c.Qα, c.Uα⁆ = c.Zα ∧ c.Zα ≤ Fcomm c := by
  have hc : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα, conjugate, card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hge := (one_lt_card_iff_ne_bot ⁅F.U ⊓ c.Qα, c.Uα⁆).mpr hne
  have he := eq_of_le_of_card_ge hF9 (by omega : Nat.card c.Zα ≤ Nat.card ↥⁅F.U ⊓ c.Qα, c.Uα⁆)
  exact ⟨he, he ▸ commutator_mono inf_le_left le_rfl⟩

/-- The reversed hypotheses of 14.7.39 apply the displacement argument on
the actual Uα/Zα. No ambient element interchanging both endpoints is assumed. -/
theorem reciprocal_commutator_eq_point (c : CriticalPath (L := L) F)
    {Wα : Type*} [AddCommGroup Wα] [Module (ZMod 2) Wα]
    (ρα : Representation (ZMod 2) (conjugate F.H c.conjugator) Wα)
    (a : BinaryConjugationSection (conjugate F.H c.conjugator) c.Uα c.Zα ρα)
    (y : conjugate F.H c.conjugator) (hy : (y : G) ∈ F.U)
    (hdisp : Module.finrank (ZMod 2) (ρα y - LinearMap.id).range = 2)
    (hcodim : Module.finrank (ZMod 2) (a.imageSpace (c.Uα ⊓ F.H.pCoreIn 2)) + 1 ≥
      Module.finrank (ZMod 2) Wα)
    (hF9 : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≠ ⊥ ∧
      ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1 ∧ F.Vi 1 ≤ Fcomm c := by
  let : Finite Wα := Finite.of_surjective (fun x : c.Uα => (a.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp a.onto)
  have hn : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≠ ⊥ := by
    intro hz
    have hb : ⁅F.U, c.Uα ⊓ F.H.pCoreIn 2⁆ ≤ c.Zα := by
      rw [commutator_comm, hz]
      exact bot_le
    have hfix := a.fixed_on_imageSpace_of_commutator_le F.U (c.Uα ⊓ F.H.pCoreIn 2) hb y hy
    have hle : a.imageSpace (c.Uα ⊓ F.H.pCoreIn 2) ≤ (ρα y - LinearMap.id).ker := by
      intro w hw
      exact sub_eq_zero.mpr (hfix w hw)
    have hd := Submodule.finrank_mono hle
    have hr := (ρα y - LinearMap.id).finrank_range_add_finrank_ker
    rw [hdisp] at hr
    omega
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hge := (one_lt_card_iff_ne_bot ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆).mpr hn
  have he := eq_of_le_of_card_ge hF9 (by omega :
    Nat.card (F.Vi 1) ≤ Nat.card ↥⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆)
  have hm : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ ⁅c.Uα, F.U⁆ := commutator_mono inf_le_left le_rfl
  rw [he, commutator_comm] at hm
  exact ⟨hn, he, hm⟩

/-- Centrality of the chosen actor in the literal quotient makes its
original displacement T-invariant, even when the lift does not commute. -/
theorem displacement_invariant (s : d.ActionDescent) (h : F.H)
    (hc : ∀ t : actorT (F := F), Commute (d.qH (t : F.H)) (d.qH h))
    (t : actorT (F := F)) (w : W) (hw : w ∈ (d.action h - LinearMap.id).range) :
    d.action (t : F.H) w ∈ (d.action h - LinearMap.id).range := by
  obtain ⟨x, rfl⟩ := hw
  refine ⟨d.action (t : F.H) x, ?_⟩
  change d.action h (d.action (t : F.H) x) - d.action (t : F.H) x =
    d.action (t : F.H) (d.action h x - x)
  rw [map_sub]
  congr 1
  rw [← s.original h, ← s.original (t : F.H)]
  have he := congrArg (fun a => s.action a x) (hc t).eq
  simpa only [map_mul, Module.End.mul_apply] using he.symm

/-- The two actual complements have the same fixed line on the same p.
Their intersection and its fixedness are conclusions of the dimension argument. -/
theorem original_common_fixed_line (c : CriticalPath (L := L) F)
    (separation : d.ModuleSeparation) (s : d.ActionDescent)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hc : ∀ x : actorT (F := F), Commute (d.qH (x : F.H)) (d.qH h))
    (hF : tilde d (Fcomm c) = (d.action h - LinearMap.id).range)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker)
    (hupper : ∀ a : SL2FourNatural.F, alternatingActor d.naturalQuotient
      (SL2FourNatural.upper a) ∈ (actorT (F := F)).map d.qH)
    (hrank : primeRank 2 d.U₀ ≤ 2) :
    tilde d (Fcomm c) ⊓ fixedT d = tilde d V ⊓ fixedT d ∧
      tilde d V ⊓ fixedT d = tilde d (F.Vi 2) := by
  let := finite_original d
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  let P : Sylow 2 ChapterJ.S5 := TH.mapSurjective d.qH_surjective
  have hTP : (actorT (F := F)).map d.qH = (P : Subgroup ChapterJ.S5) :=
    (Sylow.coe_mapSurjective d.qH_surjective TH).symm
  have hupperP a : alternatingActor d.naturalQuotient (SL2FourNatural.upper a) ∈ P :=
    show _ ∈ (P : Subgroup ChapterJ.S5) from hTP ▸ hupper a
  obtain ⟨hd, he⟩ := s.original_upper_complement h t ht hh
  have hFV : tilde d (Fcomm c) ≤ tilde d V ⊔ d.projection.toLinearMap.ker := by
    rw [hF, ← h65, he]
    exact le_sup_left
  have hnF : ∀ x : actorT (F := F), ∀ w ∈ tilde d (Fcomm c),
      d.action x w ∈ tilde d (Fcomm c) := by
    rw [hF]
    exact displacement_invariant d s h hc
  have hnV : ∀ x : actorT (F := F), ∀ w ∈ tilde d V, d.action x w ∈ tilde d V :=
    tilde_invariant d (by simpa only [F.last] using F.invariant 3)
  have hmapV : (tilde d V).map d.projection.toLinearMap = SL2FourNatural.upperFixed :=
    upper_complement_image d.naturalQuotient s.projection d.projection_onto s.kernel_fixed _ h65
  have hmapF : (tilde d (Fcomm c)).map d.projection.toLinearMap = SL2FourNatural.upperFixed := by
    rw [hF]
    exact upper_complement_image d.naturalQuotient s.projection d.projection_onto s.kernel_fixed _ he
  have hfixF := original_complement_fixed_finrank d.naturalQuotient d.action d.qH d.projection
    (actorT (F := F)) P hTP hupperP (tilde d (Fcomm c)) hnF (hF ▸ hd) hmapF
  have hfixV := original_complement_fixed_finrank d.naturalQuotient d.action d.qH d.projection
    (actorT (F := F)) P hTP hupperP (tilde d V) hnV (seed_disjoint_kernel d separation) hmapV
  constructor
  · exact common_fixed_line (d.action.comp (actorT (F := F)).subtype)
      (tilde d (Fcomm c)) (tilde d V) d.projection.toLinearMap.ker
      (hF ▸ displacement_finrank d s h t ht hh) (seed_tilde_finrank d)
      (kernel_finrank_le_one d hrank) hFV hnF hnV hfixF hfixV
  · exact (Submodule.eq_of_le_of_finrank_eq
      (le_inf (d.conjugationSection.imageSpace_mono (F.le_seed 2)) (plane_tilde_fixed d))
      ((plane_tilde_finrank d).trans hfixV.symm)).symm


include d in
/-- Placement in H makes the actual commutator a subgroup of U. -/
theorem Fcomm_le_U (c : CriticalPath (L := L) F) (earlier : c.EarlierImages) :
    Fcomm c ≤ F.U :=
  le_normalizer_iff_commutator_le_left.mp
    ((c.Uα_le_H earlier).trans d.conjugationSection.normalized)

/-- The careful rechoice and the same-p complement calculation imply the
literal point containment. This is the fixed-line step in 14.7.70. -/
theorem selected_point_le_plane (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (separation : d.ModuleSeparation) (s : d.ActionDescent)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hc : ∀ x : actorT (F := F), Commute (d.qH (x : F.H)) (d.qH h))
    (hF : tilde d (Fcomm c) = (d.action h - LinearMap.id).range)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker)
    (hupper : ∀ a : SL2FourNatural.F, alternatingActor d.naturalQuotient
      (SL2FourNatural.upper a) ∈ (actorT (F := F)).map d.qH)
    (hrank : primeRank 2 d.U₀ ≤ 2) (hZF : c.Zα ≤ Fcomm c)
    (hchoice : c.Zα ≤ F.Vi 2 ⊔ d.U₀) : c.Zα ≤ F.Vi 2 := by
  obtain ⟨he, hp⟩ := original_common_fixed_line d c separation s h t ht hh hc hF h65 hupper hrank
  apply (tilde_le_iff d (hZF.trans (Fcomm_le_U d c earlier))
    ((F.le_seed 2).trans (Data.V_le_U F)) (F.monotone (by decide : 1 ≤ 2))).mp
  rw [← hp, ← he]
  exact le_inf (d.conjugationSection.imageSpace_mono hZF)
    (selected_point_fixed d c hrank hchoice)

/-- Both complement descriptions lift to the actual product with U₀. -/
theorem commutator_sup_U₀ (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hF : tilde d (Fcomm c) = (d.action h - LinearMap.id).range)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker) : Fcomm c ⊔ d.U₀ = d.U₀ ⊔ V := by
  have hfU := Fcomm_le_U d c earlier
  have he : tilde d (Fcomm c ⊔ d.U₀) = tilde d (d.U₀ ⊔ V) := by
    rw [tilde_sup d hfU d.U₀_le_U, tilde_sup d d.U₀_le_U (Data.V_le_U F), tilde_U₀ d, hF,
      ← (s.original_upper_complement h t ht hh).2, h65, sup_comm]
  exact le_antisymm
    ((tilde_le_iff d (sup_le hfU d.U₀_le_U) (sup_le d.U₀_le_U (Data.V_le_U F))
      (d.point_le_U₀.trans le_sup_left)).mp he.le)
    ((tilde_le_iff d (sup_le d.U₀_le_U (Data.V_le_U F)) (sup_le hfU d.U₀_le_U)
      (d.point_le_U₀.trans le_sup_right)).mp he.ge)

/-- The rank-three disjointness calculation in the marked cover implies
Zα is outside V, using precisely the preceding fusion exclusion Zα not≤U₀. -/
theorem point_not_le_seed (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hZF : c.Zα ≤ Fcomm c)
    (hZ₀ : ¬ c.Zα ≤ d.U₀) (hd : Disjoint (tilde d (Fcomm c)) (tilde d V)) :
    ¬ c.Zα ≤ V := by
  intro hZV
  apply hZ₀
  apply (tilde_le_iff d (hZF.trans (Fcomm_le_U d c earlier)) d.U₀_le_U d.point_le_U₀).mp
  rw [tilde_U₀ d]
  have hle : tilde d c.Zα ≤ tilde d (Fcomm c) ⊓ tilde d V :=
    le_inf (d.conjugationSection.imageSpace_mono hZF) (d.conjugationSection.imageSpace_mono hZV)
  exact (hle.trans_eq hd.eq_bot).trans bot_le


/-- The nonidentity upper actor has exactly the upper four-group's fixed
space on the original cover. -/
theorem actor_fixed_iff (s : d.ActionDescent) (h : F.H)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) (w : W) :
    d.action h w = w ↔
      w ∈ SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) := by
  let p := restrictedProjection d.naturalQuotient s.projection
  have hp := SL2FourCentralCover.isCover_of_natural_indecomposable p d.projection_onto
    s.kernel_fixed s.indecomposable
  rw [← s.original h, hh]
  exact (SL2FourCentralCover.quotient_upper_fixed_iff p hp t ht w).trans
    (SL2CentralExtension.mem_upperFixed_iff _ p.toLinearMap d.projection_onto
      (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v)
      (fun v hv g => s.kernel_fixed hv g) w).symm

/-- The upper bound in (*) is proved from commutativity of the actual
conjugate Uα and the original section's fixed-space computation. -/
theorem intersection_le_U₀_sup_seed (c : CriticalPath (L := L) F)
    (s : d.ActionDescent) (h : F.H) (hmem : (h : G) ∈ c.Uα)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker) : F.U ⊓ c.Uα ≤ d.U₀ ⊔ V := by
  let : IsMulCommutative F.U := d.abelian
  let : IsMulCommutative c.Uα := Subgroup.map_isMulCommutative F.U (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let : CommGroup c.Uα := IsMulCommutative.instCommGroup
  apply (tilde_le_iff d inf_le_left (sup_le d.U₀_le_U (Data.V_le_U F))
    (d.point_le_U₀.trans le_sup_left)).mp
  rw [tilde_sup d d.U₀_le_U (Data.V_le_U F), tilde_U₀ d, sup_comm, ← h65]
  intro w hw
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  apply (actor_fixed_iff d s h t ht hh _).mp
  have hc : (h : G) * a = (a : G) * h :=
    congrArg Subtype.val (mul_comm (⟨h, hmem⟩ : c.Uα) ⟨a, ha.2⟩)
  have he : (h : G) * a * (h : G)⁻¹ = a := by rw [hc, mul_inv_cancel_right]
  exact (d.conjugationSection.equivariant h a).symm.trans
    (congrArg (fun x : F.U => (d.conjugationSection.coordinates x).toAdd) (Subtype.ext he))

/-- The marked-cover spanning computation lifts to the actual product FV.
The spanning premise is a remaining local calculation, not an earlier theorem. -/
theorem commutator_sup_seed (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker)
    (hspan : tilde d (Fcomm c) ⊔ tilde d V =
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient))) :
    Fcomm c ⊔ V = d.U₀ ⊔ V := by
  have hfU := Fcomm_le_U d c earlier
  have he : tilde d (Fcomm c ⊔ V) = tilde d (d.U₀ ⊔ V) := by
    rw [tilde_sup d hfU (Data.V_le_U F), tilde_sup d d.U₀_le_U (Data.V_le_U F),
      tilde_U₀ d, hspan, h65, sup_comm]
  exact le_antisymm
    ((tilde_le_iff d (sup_le hfU (Data.V_le_U F)) (sup_le d.U₀_le_U (Data.V_le_U F))
      (d.point_le_U₀.trans le_sup_left)).mp he.le)
    ((tilde_le_iff d (sup_le d.U₀_le_U (Data.V_le_U F)) (sup_le hfU (Data.V_le_U F))
      ((F.le_seed 1).trans le_sup_right)).mp he.ge)

/-- All three source intersection equalities, after the fixed-line step and
14.7.3(4) have supplied the L-conjugate. The mutual normalization input is
precisely F.9.13(3); the two section inputs use the same original p. -/
theorem intersection_equalities (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent)
    (h : F.H) (hmem : (h : G) ∈ c.Uα)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hF : tilde d (Fcomm c) = (d.action h - LinearMap.id).range)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker)
    (hspan : tilde d (Fcomm c) ⊔ tilde d V =
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)))
    (hmutual : F.U ≤ normalizer (c.Uα : Set G))
    (l : G) (hl : l ∈ L) (hconj : c.Uα = conjugate F.U l) :
    F.U ⊓ c.Uα = d.U₀ ⊔ V ∧ F.U ⊓ c.Uα = Fcomm c ⊔ V ∧
      F.U ⊓ c.Uα = Fcomm c ⊔ d.U₀ := by
  have hV : V ≤ c.Uα := by
    calc
      V = conjugate V l := ((conjugate_eq_iff V l).mpr (d.natural.chosen.normalizes hl)).symm
      _ ≤ conjugate F.U l := map_mono (Data.V_le_U F)
      _ = c.Uα := hconj.symm
  have hFα : Fcomm c ≤ c.Uα := le_normalizer_iff_commutator_le_right.mp hmutual
  have hjoin := commutator_sup_seed d c earlier s h65 hspan
  have he : F.U ⊓ c.Uα = d.U₀ ⊔ V := le_antisymm
    (intersection_le_U₀_sup_seed d c s h hmem t ht hh h65)
    (hjoin ▸ sup_le (le_inf (Fcomm_le_U d c earlier) hFα) (le_inf (Data.V_le_U F) hV))
  exact ⟨he, he.trans hjoin.symm,
    he.trans (commutator_sup_U₀ d c earlier s h t ht hh hF h65).symm⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry
