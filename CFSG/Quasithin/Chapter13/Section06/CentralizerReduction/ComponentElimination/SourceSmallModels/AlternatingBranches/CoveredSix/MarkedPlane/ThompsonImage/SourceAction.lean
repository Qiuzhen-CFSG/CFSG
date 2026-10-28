module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.Basic
public import Theory.GroupTheory.PCoreImage

/-!
# The full plus action required by the Thompson marking

`PlusBlockModel` records an embedding of the whole plus actor into the actual
hexacode automorphism group, extending the prescribed even component and
retaining conjugation on the original U(K). It contains no Thompson marking,
offender classification, fixed dimension or normalizer conclusion.

The supplied action makes the Baumann fixed-vector argument available on
U(K) itself. Together with pointwise-kernel recognition this discharges the
Baumann-image premise of the existing source normalizer-image theorem.
Construction of the model remains a separate source obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the covered
A₆ paragraph of 13.6.22, printed p.932. The concrete model is the licensed
ATLAS-derived hexacode used by `CoveredSix.HexacodeModel`.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (m : HexacodeModel h)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)

omit [IsElementaryAbelian 2 (blockU K)] in
/-- The block layer lies in the original Tᵥ: its two-core is normal in KTᵥ,
and the local-family condition makes Tᵥ Sylow in that actual overgroup. -/
theorem blockU_le_Tv (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    (blockU K).map K.subtype ≤ Tv T v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : K.pCoreIn 2 ≤ (K ⊔ Tv T v).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer hn)
  obtain ⟨P, hP⟩ := hK.1.2.2.1
  exact (map_mono (blockU_le_core (L := K))).trans
    (hc.trans ((pCoreIn_le_sylow (K ⊔ Tv T v) P).trans_eq hP))

/-- A model of the full source action, including the actual even inclusion.
This is an action specification, not an assumed four-group marking. -/
structure PlusBlockModel where
  embedding : Gplus K L T z v hL hz →* Atlas.Codes.HexAutomorphisms
  injective : Function.Injective embedding
  component : ∀ a, embedding (f a) = (m.quotientIso a).val
  conjugation : ∀ (g : plusActor K L T v) (u : Additive (blockU K)),
    (((m.coordinates.symm
      (Hexacode.action (embedding (plusMk K L T z v hL hz g)) (m.coordinates u))).toMul : K) : G) =
        (g : G) * ((u.toMul : K) : G) * (g : G)⁻¹

variable {K L T z v h hL hz m f}
variable (d : PlusBlockModel K L T z v h hL hz m f)

/-- Transport the full hexacode action to the original block layer. -/
noncomputable def PlusBlockModel.action :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive (blockU K)) where
  toFun g := m.coordinates.symm.toLinearMap.comp
    ((Hexacode.action (d.embedding g)).comp m.coordinates.toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro u
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    simp

/-- The coordinates intertwine the full action, not only its even restriction. -/
theorem PlusBlockModel.intertwining (g : Gplus K L T z v hL hz) (u : Additive (blockU K)) :
    m.coordinates (d.action g u) = Hexacode.action (d.embedding g) (m.coordinates u) :=
  m.coordinates.apply_symm_apply _

/-- Agreement with the previously constructed action of K/O₂(K). -/
theorem PlusBlockModel.action_component (a : K ⧸ pCore 2 K) (u : Additive (blockU K)) :
    d.action (f a) u = binaryAction h a u := by
  apply m.coordinates.injective
  rw [d.intertwining, d.component, m.intertwining]

/-- The fixed spaces agree literally on the original U(K). -/
theorem PlusBlockModel.fixedSpace_component (A : Subgroup (K ⧸ pCore 2 K)) :
    fixedSpace d.action (A.map f) = fixedSpace (binaryAction h) A := by
  ext u
  constructor
  · intro hu a
    have ha := hu ⟨f a, mem_map_of_mem f a.property⟩
    change d.action (f a) u = u at ha
    change binaryAction h a u = u
    simpa only [d.action_component] using ha
  · intro hu a
    obtain ⟨b, hb, he⟩ := a.property
    change d.action a.val u = u
    rw [← he, d.action_component]
    exact hu ⟨b, hb⟩

/-- Recognition of the full plus kernel also recognizes the core kernel.
No second finite normalizer calculation is needed after marking the image. -/
theorem PlusBlockModel.core_kernel_of_image (fi : Function.Injective f)
    (A : Subgroup (K ⧸ pCore 2 K))
    (hfull : subspaceKernel d.action (fixedSpace d.action (A.map f)) ⊤ = A.map f) :
    A = subspaceKernel (binaryAction h) (fixedSpace (binaryAction h) A) ⊤ := by
  apply le_antisymm
  · intro a ha
    exact ⟨mem_top _, fun u hu => hu ⟨a, ha⟩⟩
  · intro a ha
    have hm : f a ∈ A.map f := by
      rw [← hfull]
      refine ⟨mem_top _, ?_⟩
      intro u hu
      rw [d.fixedSpace_component] at hu
      rw [d.action_component]
      exact ha.2 u hu
    obtain ⟨b, hb, he⟩ := hm
    exact fi he ▸ hb

/-- The full action still acts by the original ambient conjugation. -/
theorem PlusBlockModel.action_conjugation
    (g : plusActor K L T v) (u : Additive (blockU K)) :
    (((d.action (plusMk K L T z v hL hz g) u).toMul : K) : G) =
      (g : G) * ((u.toMul : K) : G) * (g : G)⁻¹ := d.conjugation g u

/-- Faithfulness of the full model on the actual block layer. -/
theorem PlusBlockModel.action_injective : Function.Injective d.action := by
  intro a b he
  apply d.injective
  apply Hexacode.action_injective
  apply LinearMap.ext
  intro w
  have hc := congrArg m.coordinates (LinearMap.congr_fun he (m.coordinates.symm w))
  simpa only [d.intertwining, m.coordinates.apply_symm_apply] using hc

/-- The fixed space uses the full preimage of the literal plus subgroup. -/
theorem PlusBlockModel.mem_fixedSpace_image (D : Subgroup G)
    (hD : D ≤ plusActor K L T v) (u : Additive (blockU K)) :
    u ∈ fixedSpace d.action (plusImage K L T z v hL hz D) ↔
      ((u.toMul : K) : G) ∈ centralizer (D : Set G) := by
  constructor
  · intro hu g hg
    have he := congrArg (fun w : Additive (blockU K) => ((w.toMul : K) : G))
      (hu ⟨plusMk K L T z v hL hz ⟨g, hD hg⟩,
        mem_map.mpr ⟨⟨g, hD hg⟩, hg, rfl⟩⟩)
    change (((d.action (plusMk K L T z v hL hz ⟨g, hD hg⟩) u).toMul : K) : G) = _ at he
    rw [d.action_conjugation] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hu a
    obtain ⟨g, hg, he⟩ := a.property
    change d.action a.val u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [d.action_conjugation, hu g hg, mul_inv_cancel_right]

/-- Baumann fixes the Thompson-fixed vectors in U(K). Only containment of
the elementary block layer in Tᵥ is needed from the earlier Sylow setup. -/
theorem PlusBlockModel.baumann_fixes [Finite G]
    (hUT : (blockU K).map K.subtype ≤ Tv T v) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      subspaceKernel d.action
        (fixedSpace d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))) ⊤ := by
  rintro b ⟨g, hg, rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro u hu
  have hJS : elementaryAbelianMaxJ (Tv T v) ≤ Tv T v := sSup_le fun _ hA => hA.1
  have huC := (d.mem_fixedSpace_image _ (hJS.trans le_sup_right) u).mp hu
  have hu2 : ((u.toMul : K) : G) ^ 2 = 1 :=
    congrArg K.subtype (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ u.toMul.property)
  let : IsElementaryAbelian 2 (zpowers ((u.toMul : K) : G)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hu2
  have huOmega := elementary_centralizer_maxJ_le_omegaCenter (Tv T v)
    (zpowers ((u.toMul : K) : G))
    (zpowers_le.mpr (hUT (mem_map_of_mem K.subtype u.toMul.property)))
    (zpowers_le.mpr huC) (mem_zpowers ((u.toMul : K) : G))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [d.action_conjugation]
  have hc := hg.2 _ huOmega
  change ((u.toMul : K) : G) * (g : G) = (g : G) * ((u.toMul : K) : G) at hc
  rw [← hc, mul_inv_cancel_right]

/-- Recognizing the full pointwise kernel discharges the Baumann-image
identity on the original U(K), without a splitting assumption on W_K. -/
theorem PlusBlockModel.baumann_eq_thompson [Finite G]
    (hUT : (blockU K).map K.subtype ≤ Tv T v)
    (hk : subspaceKernel d.action
      (fixedSpace d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))) ⊤ =
        plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) := by
  apply le_antisymm ((d.baumann_fixes hUT).trans hk.le)
  apply map_mono
  apply comap_mono
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj w hw
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 j hj).symm

/-- Application to the existing source normalizer-image theorem. The full
kernel calculation supplies S⁺=J(Tᵥ)⁺; the core kernel supplies its normalizer. -/
theorem PlusBlockModel.source_normalizer_images_eq [Finite G]
    (hUT : (blockU K).map K.subtype ≤ Tv T v)
    (hk : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v))
    (fi : Function.Injective f)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
    (A : Subgroup (K ⧸ pCore 2 K))
    (hA : A.map f = plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))
    (hfull : subspaceKernel d.action
      (fixedSpace d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))) ⊤ =
        plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) :
    plusImage K L T z v hL hz (K ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G)) =
      plusImage K L T z v hL hz (K ⊓ normalizer (fixedSubgroup K A : Set G)) := by
  apply CoveredSix.source_normalizer_images_eq K L T z v h hL hz hk A f fi hf
  · exact (d.baumann_eq_thompson hUT hfull).trans hA.symm
  · apply fixedSpace_stabilizer_le_normalizer_of_kernel K h A
    apply d.core_kernel_of_image fi A
    simpa only [hA] using hfull

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage
