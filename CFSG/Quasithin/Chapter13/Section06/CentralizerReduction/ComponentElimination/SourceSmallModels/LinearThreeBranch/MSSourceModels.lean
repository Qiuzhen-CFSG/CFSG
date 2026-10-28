module

public import Theory.GroupTheory.PGroup.SubnormalCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.Models
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CenterPreimage

/-!
# Realizing the source MS sections in the L₃(2) branch

The five C.1.34 alternatives give modules on different literal sections of
Q=[O₂(KR),K]. We construct their ambient conjugation quotient models and
retain the common actor induced by the given K/O₂(K) identification. For
trivial-denominator natural sections, absence of fixed vectors proves that
the centralizer kernel is trivial; case (5) retains its specified centralizer.

Subnormality and two-perfection identify Q with the intrinsic core commutator.
In cases (1) and (2), equivariance proves that O₂(K) centralizes Q. This proves
both U=[Z(O₂(K)),K]=Q and [Z₀,K]=U, where Z₀ uses the restriction of the literal
checked quotient map. The same center argument applies to ordinary blocks.

These are source realization steps, not the completed 13.6.22 branch. The
nonabelian alternatives still require their center argument, and the actual
seed module U_K=[W_K,K] must still be identified with U. In particular, the
order-16 extension is retained as an honest quotient model; no splitting,
invariant-line obstruction or parabolic marking is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34,
printed pp.136–137, and 13.6.22, printed pp.932–933.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {K D E : Subgroup G} {a : K →* A} {ρ : Representation (ZMod 2) A V}

/-- A section with a central denominator and no fixed vectors has exactly the
centralizer as its denominator. Surjectivity refers to the original actor. -/
theorem section_centralizer_eq (h : HasSectionModel K D E a ρ)
    (ha : Function.Surjective a) (hE : E ≤ centralizer (K : Set G))
    (hfixed : ∀ w : V, (∀ g : A, ρ g w = w) → w = 0) :
    (centralizer (K : Set G)).subgroupOf D = E.subgroupOf D := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  let := hn
  apply le_antisymm _ (comap_mono hE)
  intro d hd
  have hz : Multiplicative.toAdd (e (QuotientGroup.mk' _ d)) = 0 := by
    apply hfixed
    intro g
    obtain ⟨k, rfl⟩ := ha g
    apply (he k d d ?_).symm
    rw [show (k : G) * (d : G) = (d : G) * (k : G) from hd k k.property,
      mul_inv_cancel_right]
  have hq : QuotientGroup.mk' (E.subgroupOf D) d = 1 :=
    e.injective (hz.trans (map_one e).symm)
  change d ∈ E.subgroupOf D
  exact (QuotientGroup.eq_one_iff d).mp hq

/-- Convert a genuine C.1.34 section to the ambient quotient model without
changing its actor or replacing its kernel by an arbitrary central subgroup. -/
theorem model_of_section (h : HasSectionModel K D E a ρ)
    (hE : (centralizer (K : Set G)).subgroupOf D = E.subgroupOf D) :
    ∃ m : ConjugationQuotientModel K D ρ, m.actor = a := by
  obtain ⟨_, hKD, _, hn, e, he⟩ := h
  exact ⟨of_section_model a hKD hn e he hE, rfl⟩

theorem model_of_fixedFree_section (h : HasSectionModel K D E a ρ)
    (ha : Function.Surjective a) (hE : E ≤ centralizer (K : Set G))
    (hfixed : ∀ w : V, (∀ g : A, ρ g w = w) → w = 0) :
    ∃ m : ConjugationQuotientModel K D ρ, m.actor = a :=
  model_of_section h (section_centralizer_eq h ha hE hfixed)

variable {R S : Subgroup G}

/-- The actor used in C.1.34 is the actual two-core quotient map. -/
theorem linearThreeActor_surjective
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Function.Surjective (linearThreeActor e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem linearThreeActor_kernel
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    (linearThreeActor e).ker = pCore 2 K := by
  ext k
  change e (QuotientGroup.mk' (pCore 2 K) k) = 1 ↔ k ∈ pCore 2 K
  rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- The trivial-denominator natural section has no nontrivial centralizer. -/
theorem natural_model_of_section
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    ∃ m : ConjugationQuotientModel K D BinaryLinearThree.W,
      m.actor = linearThreeActor e := by
  apply model_of_fixedFree_section h (linearThreeActor_surjective e) bot_le
  intro w hw
  exact BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero w (fun g _ => hw g)

/-- Both summands retain the same core-quotient identification. -/
theorem doubled_model_of_section
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D ⊥ (linearThreeActor e)
      (BinaryLinearThree.W.prod BinaryLinearThree.W)) :
    ∃ m : ConjugationQuotientModel K D (BinaryLinearThree.W.prod BinaryLinearThree.W),
      m.actor = linearThreeActor e := by
  apply model_of_fixedFree_section h (linearThreeActor_surjective e) bot_le
  intro w hw
  exact BinaryLinearThree.ParabolicFixedFree.doubled_fixed_eq_zero w (fun g _ => hw g)

/-- Case (5) already specifies the literal centralizer denominator. -/
theorem central_extension_model_of_section
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D (D ⊓ centralizer (K : Set G))
      (linearThreeActor e) BinaryLinearThree.W) :
    ∃ m : ConjugationQuotientModel K D BinaryLinearThree.W,
      m.actor = linearThreeActor e := by
  apply model_of_section h
  ext d
  change (d : G) ∈ centralizer (K : Set G) ↔
    (d : G) ∈ D ⊓ centralizer (K : Set G)
  exact ⟨fun hd => ⟨d.property, hd⟩, fun hd => hd.2⟩

/-- Realize every C.1.34 alternative on its specified carrier. The center and
its moved subgroup remain distinct from Q until the source identifies U. -/
theorem models_of_msModuleAlternatives
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : MSModuleAlternatives K R S 1 (ZMod 2) e) :
    (∃ m : ConjugationQuotientModel K (msQ K R) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∨
    (∃ m : ConjugationQuotientModel K (msQ K R)
      (BinaryLinearThree.W.prod BinaryLinearThree.W), m.actor = linearThreeActor e) ∨
    (∃ m : ConjugationQuotientModel K (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ K R)) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∨
    (∃ m : ConjugationQuotientModel K ⁅Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ K R), K⁆ BinaryLinearThree.W,
      m.actor = linearThreeActor e) := by
  rcases h with h | h | h | h | h
  · exact Or.inl (natural_model_of_section e h.2.2)
  · exact Or.inr (Or.inl (doubled_model_of_section e h.1))
  · exact Or.inr (Or.inr (Or.inl (natural_model_of_section e h.1)))
  · exact Or.inr (Or.inr (Or.inr (natural_model_of_section e h.2.2.2.2.2.1)))
  · exact Or.inl (central_extension_model_of_section e h.2.2.1)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels

variable {G : Type*} [Group G] [Finite G]

/-- The C.1.34 core commutator, transported into K with no equality between
K and its action quotient. -/
theorem msQ_eq_ambient_blockU (K R : Subgroup G)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K) :
    msQ K R = (blockU K).map K.subtype := by
  let H := K ⊔ R
  let B := K.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  have hb : B.map H.subtype = K := map_subgroupOf_eq_of_le le_sup_left
  have he : (blockU B).map e.toMonoidHom = blockU K := by
    rw [blockU, map_commutator, pCore_map_iso, map_top_of_surjective _ e.surjective]
    rfl
  have hc := commutator_le_core_commutator_of_isSubnormal B (pCore 2 H) hs
    (hp.of_surjective e.symm.toMonoidHom e.symm.surjective)
    pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator, hb] at hm
  have hf : H.subtype.comp B.subtype = K.subtype.comp e.toMonoidHom := rfl
  rw [map_map, hf, ← map_map] at hm
  change msQ K R ≤ ((blockU B).map e.toMonoidHom).map K.subtype at hm
  rw [he] at hm
  apply le_antisymm hm
  change (⁅pCore 2 K, (⊤ : Subgroup K)⁆).map K.subtype ≤ _
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact commutator_mono (pCoreAmbient_mono_of_isSubnormalIn K H 2 le_sup_left hs) le_rfl

/-- The literal ambient center commutator used in 13.6.22. -/
noncomputable def sourceU (K : Subgroup G) : Subgroup G :=
  ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆

/-- The restriction of C_G(v)→C_G(v)/⟨v⟩ to K defines exactly the source Z₀. -/
noncomputable abbrev sourceZ0 (K : Subgroup G) (v : G) (hK : K ≤ Gv v) : Subgroup G :=
  BinaryRankTwo.CenterPreimage.sourceZ0 K v hK

variable {J H : Type*} [Group J] [Group H] [Finite J]

/-- Centrality of the core commutator suffices; irreducibility is not required,
so this also applies to a doubled natural module. -/
theorem center_preimage_commutator_of_central (hp : IsPPerfect 2 J)
    (hc : blockU J ≤ centralizer (pCore 2 J : Set J))
    (f : J →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    ⁅((center (pCore 2 H)).map (pCore 2 H).subtype).comap f,
      (⊤ : Subgroup J)⁆ = blockU J := by
  let : Finite H := Finite.of_surjective f hf
  have hid : ⁅blockU J, (⊤ : Subgroup J)⁆ = blockU J :=
    commutator_isPPerfect_idempotent ⊤ (pCore 2 J)
      (hp.of_surjective (topEquiv (G := J)).symm.toMonoidHom
        (topEquiv (G := J)).symm.surjective)
      pCore_isPGroup (by rw [normalizer_eq_top])
  have hcore : (pCore 2 H).comap f = pCore 2 J :=
    f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore 2 J).map f = pCore 2 H := by
    rw [← hcore, map_comap_eq_self_of_surjective hf]
  have hupper : ((center (pCore 2 H)).map (pCore 2 H).subtype).comap f ≤ pCore 2 J := by
    rw [← hcore]
    exact comap_mono (map_subtype_le _)
  have hlower : blockU J ≤
      ((center (pCore 2 H)).map (pCore 2 H).subtype).comap f := by
    intro u hu
    refine ⟨⟨f u, ?_⟩, ?_, rfl⟩
    · rw [← hmap]
      exact mem_map_of_mem f (blockU_le_core hu)
    · apply mem_center_iff.mpr
      intro x
      have hx : (x : H) ∈ (pCore 2 J).map f := hmap.symm ▸ x.property
      obtain ⟨y, hy, he⟩ := hx
      apply Subtype.ext
      change (x : H) * f u = f u * (x : H)
      rw [← he, ← map_mul, ← map_mul]
      exact congrArg f (mem_centralizer_iff.mp (hc hu) y hy)
  exact le_antisymm (commutator_mono hupper le_rfl)
    (hid.symm.le.trans (commutator_mono hlower le_rfl))

theorem sourceU_eq_of_central (K : Subgroup G) (hp : IsPPerfect 2 K)
    (hc : blockU K ≤ centralizer (pCore 2 K : Set K)) :
    sourceU K = (blockU K).map K.subtype := by
  have h := center_preimage_commutator_of_central hp hc (MonoidHom.id K)
    Function.surjective_id (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
  have hm := congrArg (map K.subtype) h
  rw [comap_id, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The actual checked-center identity for every central core commutator. -/
theorem sourceZ0_commutator_of_central (K : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1) (hp : IsPPerfect 2 K)
    (hc : blockU K ≤ centralizer (pCore 2 K : Set K)) :
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  have h := center_preimage_commutator_of_central hp hc
    (BinaryRankTwo.CenterPreimage.checkedKMap K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_surjective K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_pKernel K v hK hv)
  have hm := congrArg (map K.subtype) h
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.trans (sourceU_eq_of_central K hp hc).symm

/-- A linear block gives both the literal source U-model and the checked-center
identity, with its original core-quotient identification recorded. -/
theorem linearTwoBlock_realization (K : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1) (h : IsLinearTwoBlock K 3) :
    (∃ e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
        m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  refine ⟨?_, sourceZ0_commutator_of_central K v hK hv h.2.1.twoPerfect h.2.1.central⟩
  obtain ⟨r, ⟨b⟩, hr⟩ := h.2.2.2
  refine ⟨b.quotientIso, ?_⟩
  rw [sourceU_eq_of_central K h.2.1.twoPerfect h.2.1.central]
  exact ⟨of_block_model K BinaryLinearThree.W r b hr, rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
variable {G : Type*} [Group G] {K D : Subgroup G}

/-- A section with trivial denominator, acted on through K/O₂(K), is
centralized by the actual ambient image of O₂(K). -/
theorem core_centralizes_trivial_section
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (h : HasSectionModel K D ⊥ (linearThreeActor e) ρ) :
    K.pCoreIn 2 ≤ centralizer (D : Set G) := by
  obtain ⟨_, hKD, _, hn, f, he⟩ := h
  let := hn
  have hi : Function.Injective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf D)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', bot_subgroupOf]
  rintro x ⟨k, hk, rfl⟩ d hd
  let d' := D.normalizerMonoidHom ⟨k, hKD k.property⟩ ⟨d, hd⟩
  have ha : linearThreeActor e k = 1 := by
    change k ∈ (linearThreeActor e).ker
    rwa [linearThreeActor_kernel]
  have hh : f (QuotientGroup.mk' _ d') = f (QuotientGroup.mk' _ ⟨d, hd⟩) := by
    apply Multiplicative.toAdd.injective
    simpa only [ha, map_one, Module.End.one_apply] using he k ⟨d, hd⟩ d' rfl
  have hd' := congrArg Subtype.val (hi (f.injective hh))
  change (k : G) * d * (k : G)⁻¹ = d at hd'
  exact (mul_inv_eq_iff_eq_mul.mp hd').symm

/-- C.1.34(1) and (2) directly give central core commutators. Consequently
both natural and doubled-natural sections satisfy the checked-center identity,
without treating the doubled module as an irreducible block. -/
theorem trivial_ms_section_realization [Finite G]
    {R : Subgroup G} (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (h : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e) ρ)
    (hfixed : ∀ w : V, (∀ g : BinaryLinearThree.Group, ρ g w = w) → w = 0) :
    sourceU K = msQ K R ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) ρ,
      m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  have hQ := msQ_eq_ambient_blockU K R hs hp
  have hcentral := core_centralizes_trivial_section e ρ h
  have hc : blockU K ≤ centralizer (pCore 2 K : Set K) := by
    intro u hu k hk
    apply Subtype.ext
    exact (hcentral (mem_map_of_mem K.subtype hk) (u : G)
      (hQ.symm ▸ mem_map_of_mem K.subtype hu)).symm
  have hU : sourceU K = msQ K R := (sourceU_eq_of_central K hp hc).trans hQ.symm
  refine ⟨hU, ?_, sourceZ0_commutator_of_central K v hK hv hp hc⟩
  rw [hU]
  exact model_of_fixedFree_section h (linearThreeActor_surjective e) bot_le hfixed

/-- Application of the whole-module natural alternative of C.1.34. -/
theorem natural_ms_section_realization [Finite G]
    {R : Subgroup G} (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    sourceU K = msQ K R ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  apply trivial_ms_section_realization v hK hv hs hp e BinaryLinearThree.W h
  intro w hw
  exact BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero w (fun g _ => hw g)

/-- Application of the doubled whole-module alternative, with one common actor. -/
theorem doubled_ms_section_realization [Finite G]
    {R : Subgroup G} (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (BinaryLinearThree.W.prod BinaryLinearThree.W)) :
    sourceU K = msQ K R ∧
    (∃ m : ConjugationQuotientModel K (sourceU K)
      (BinaryLinearThree.W.prod BinaryLinearThree.W), m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  apply trivial_ms_section_realization v hK hv hs hp e
    (BinaryLinearThree.W.prod BinaryLinearThree.W) h
  intro w hw
  exact BinaryLinearThree.ParabolicFixedFree.doubled_fixed_eq_zero w (fun g _ => hw g)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
