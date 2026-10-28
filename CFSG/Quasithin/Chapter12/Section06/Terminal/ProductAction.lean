module
public import Theory.Representation.SymmetricFiveThreeDisplacement
public import CFSG.Quasithin.ChapterF.Section09.QuinticCoreEscape
public import Theory.Representation.BinaryConjugationSection.FullMovement

/-!
# The cubic factor on the original terminal quotient

The full preimage of the normal cubic factor of the marked H/O₂(H) is
normal in H. Its placement in the image of L₁T makes it normalize V₅.
Irreducibility on V₅/V₁ forces its commutator image to be zero or full.
The zero case puts this normal preimage inside the seed centralizer core,
contradicting the nontrivial cubic image. Generation by H-conjugates then
gives full movement on U_H/V₁.

F.9.2 supplies the faithful action on the literal group quotient U_H/V₁,
with its original projection retained. The inverted-cubic coordinates
construct two faithful isomorphic S₅ summands, and every actor of displacement
at most one lies in the original O₂(H). No S₅ module classification is assumed.
The S₅ × S₃ marking and its local cubic placement remain source premises.

Source: Aschbacher–Smith, final paragraph of Section12.6, printed p.838,
using F.9.1(a),(b) and F.9.2(3), printed pp.317–318.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender InvertedCubicTensor
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Terminal
abbrev Product := Equiv.Perm (Fin 5) × S₃
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- The specified marking composed with the literal two-core quotient map. -/
def productMap (e : (D.H ⧸ pCore 2 D.H) ≃* Product) : D.H →* Product :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D.H))

/-- The normal cubic factor in S₅ × S₃. -/
def cubicFactor : Subgroup Product :=
  (alternatingGroup (Fin 3)).map (MonoidHom.inr (Equiv.Perm (Fin 5)) S₃)

instance cubicFactor_normal : cubicFactor.Normal := by
  have he : cubicFactor = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod
      (alternatingGroup (Fin 3)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rfl, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.2, hy, Prod.ext (mem_bot.mp hx).symm rfl⟩
  rw [he]
  infer_instance

/-- Its full preimage in H, embedded in the original ambient group. -/
def cubicActor (e : (D.H ⧸ pCore 2 D.H) ≃* Product) : Subgroup G :=
  (cubicFactor.comap (productMap e)).map D.H.subtype

omit [Finite G] in
theorem cubicActor_le (e : (D.H ⧸ pCore 2 D.H) ≃* Product) : cubicActor e ≤ D.H :=
  map_subtype_le _

omit [Finite G] in
theorem cubicActor_normalized (e : (D.H ⧸ pCore 2 D.H) ≃* Product) :
    D.H ≤ normalizer (cubicActor e : Set G) := by
  rw [cubicActor]
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (cubicFactor.comap (productMap e)).le_normalizer_map D.H.subtype

omit [Finite G] in
theorem cubicActor_image (e : (D.H ⧸ pCore 2 D.H) ≃* Product) :
    ((cubicActor e).subgroupOf D.H).map (productMap e) = cubicFactor := by
  rw [cubicActor, subgroupOf, comap_map_eq_self_of_injective D.H.subtype_injective]
  exact map_comap_eq_self_of_surjective
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _

include h in
/-- The local cubic placement and the proved two-core action normalize V₅. -/
theorem cubicActor_normalizes_seed_of_local_image
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e)) :
    cubicActor e ≤ normalizer (D.Vplus : Set G) := by
  have hQ : D.QH ≤ normalizer (D.Vplus : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
      h.commutator_UH_QH_le_point).trans h.point_lt.le
  rintro x ⟨xH, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := hplace hx
  have hz : y⁻¹ * xH ∈ pCore 2 D.H := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    rw [map_one]
    change productMap e (y⁻¹ * xH) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hzn : ((y⁻¹ * xH : D.H) : G) ∈ normalizer (D.Vplus : Set G) :=
    hQ (mem_map_of_mem D.H.subtype hz)
  have hm := (normalizer (D.Vplus : Set G)).mul_mem (h.local_normalizes hy) hzn
  change (y : G) * ((y : G)⁻¹ * (xH : G)) ∈ normalizer (D.Vplus : Set G) at hm
  simpa only [mul_inv_cancel_left, Subgroup.subtype_apply] using hm

include h in
/-- Seed movement propagates through the original H-conjugate span. -/
theorem full_movement (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hseed : D.Vplus = ⁅cubicActor e, D.Vplus⁆ ⊔ D.V₁) :
    D.UH = ⁅cubicActor e, D.UH⁆ ⊔ D.V₁ := by
  have hNU : D.H ≤ normalizer (D.UH : Set G) := le_normalizer_conjugateSpanBy D.Vplus D.H
  have hNX := cubicActor_normalized e
  have hNZ := h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · apply conjugateSpanBy_le
    · rw [hseed]
      exact sup_le_sup (commutator_mono le_rfl (le_conjugateSpanBy _ _)) le_rfl
    · intro g hg
      rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hNX hg),
        mem_normalizer_iff_map_conj_eq.mp (hNU hg),
        mem_normalizer_iff_map_conj_eq.mp (hNZ hg)]
  · exact sup_le
      (le_normalizer_iff_commutator_le_right.mp ((cubicActor_le e).trans hNU))
      (h.point_lt.le.trans (le_conjugateSpanBy _ _))

include h in
/-- F.9 irreducibility and the original seed-kernel core force full seed movement. -/
theorem cubic_seed_movement (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hn : cubicActor e ≤ normalizer (D.Vplus : Set G)) :
    D.Vplus = ⁅cubicActor e, D.Vplus⁆ ⊔ D.V₁ := by
  let X := cubicActor e
  let W := ⁅X, D.Vplus⁆ ⊔ D.V₁
  have hWV : W ≤ D.Vplus := sup_le
    (le_normalizer_iff_commutator_le_right.mp hn) h.point_lt.le
  have hNW : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (W : Set G) := by
    intro g hg
    change g ∈ normalizer ((⁅X, D.Vplus⁆ ⊔ D.V₁ : Subgroup G) : Set G)
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (cubicActor_normalized e (h.local_le hg)),
      mem_normalizer_iff_map_conj_eq.mp (h.local_normalizes hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) (h.local_le hg))]
  rcases h.irreducible W le_sup_right hWV hNW with he | he
  · exfalso
    let := h.point_normal
    let : (X.subgroupOf D.H).Normal :=
      normal_subgroupOf_of_le_normalizer (cubicActor_normalized e)
    have hXK : X.subgroupOf D.H ≤
        Subgroup.centralizerModulo ⊤ (D.Vplus.subgroupOf D.H)
          (D.V₁.subgroupOf D.H) := by
      intro x hx
      apply Subgroup.mem_centralizerModulo_iff.mpr
      refine ⟨mem_top _, fun v hv => ?_⟩
      have hc : ⁅X, D.Vplus⁆ ≤ D.V₁ := le_sup_left.trans he.le
      rw [commutator_comm] at hc
      exact hc (commutator_mem_commutator hv hx)
    have hXQ : X.subgroupOf D.H ≤ pCore 2 D.H :=
      (normal_le_normalCore.mpr hXK).trans h.kernel_core
    have hkill : pCore 2 D.H ≤ (productMap e).ker := by
      intro x hx
      change e (QuotientGroup.mk' (pCore 2 D.H) x) = 1
      have hxq : QuotientGroup.mk' (pCore 2 D.H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hxq, map_one]
    have hbad : cubicFactor ≤ ⊥ := by
      rw [← cubicActor_image e]
      exact ((Subgroup.map_eq_bot_iff _).mpr (hXQ.trans hkill)).le
    have hcyc : cubic ∈ alternatingGroup (Fin 3) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have hc : (1, cubic) ∈ cubicFactor := ⟨cubic, hcyc, rfl⟩
    have hc1 := congrArg Prod.snd (mem_bot.mp (hbad hc))
    exact (by decide +kernel : cubic ≠ 1) hc1
  · exact he.symm

include h in
/-- Construct the faithful literal quotient action, its cubic splitting input,
and the no-transvection conclusion used by F.9.16(1). -/
theorem exists_product_section [IsElementaryAbelian 2 D.UH]
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e)) :
    let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
    ∃ (τ : Representation (ZMod 2) Product (Additive (D.UH ⧸ D.V₁.subgroupOf D.UH)))
      (c : BinaryConjugationSection D.H D.UH D.V₁ (τ.comp (productMap e))),
      Function.Injective τ ∧
      fixedSpace (rightAction τ) (alternatingGroup (Fin 3)) = ⊥ ∧
      (∀ u : D.UH, (c.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) ∧
      ∀ b : D.H, finrank (ZMod 2) (τ (productMap e b) - LinearMap.id).range ≤ 1 →
        b ∈ pCore 2 D.H := by
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨σ, c, hσ, hc⟩ := h.faithful_UH_section
  let τ := σ.comp e.symm.toMonoidHom
  have he : τ.comp (productMap e) = σ.comp (QuotientGroup.mk' (pCore 2 D.H)) := by
    apply MonoidHom.ext
    intro a
    change σ (e.symm (e _)) = σ _
    rw [e.symm_apply_apply]
  let c' : BinaryConjugationSection D.H D.UH D.V₁ (τ.comp (productMap e)) := {
    section_le := c.section_le
    kernel_le := c.kernel_le
    normalized := c.normalized
    coordinates := c.coordinates
    onto := c.onto
    kernel_eq := c.kernel_eq
    equivariant := by intro a u; rw [he]; exact c.equivariant a u }
  have hseed := cubic_seed_movement h e (cubicActor_normalizes_seed_of_local_image h e hplace)
  have hmove := c'.subspaceCommutator_eq_top_of_movement
    (cubicActor e) (cubicActor_le e) (full_movement h e hseed)
  rw [subspaceCommutator_comp_map, cubicActor_image] at hmove
  have hfree := ambient_fixedFree_of_commutator τ (MonoidHom.inr _ _) hmove
  have hτ : Function.Injective τ := hσ.comp e.symm.injective
  have hfixed : fixedSpace (rightAction τ) (alternatingGroup (Fin 3)) = ⊥ :=
    (fixedFree_iff_fixedSpace_eq_bot _).mp hfree
  refine ⟨τ, c', hτ, hfixed, hc, ?_⟩
  intro b hb
  have hb1 := Representation.SymmetricFiveThree.no_transvection τ hτ hfixed
    (productMap e b) hb
  apply (QuotientGroup.eq_one_iff b).mp
  exact e.injective (hb1.trans (map_one e).symm)

end CFSG.Quasithin.Chapter12.Section06.Terminal
