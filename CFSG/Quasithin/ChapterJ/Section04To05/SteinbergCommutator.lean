module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.SecondCore
public import Theory.Representation.PSL3Two.SteinbergStructure.LineRadicalCommutator
public import Theory.GroupAction.Quotient

/-!
# The original second-core Steinberg commutator

The image of R₂ under the original Ru1 map is a conjugate line radical.
The concrete six-dimensional calculation therefore applies to the literal
R₂ action on S/V. Pulling this space back through the original Steinberg
coordinates defines the source S₂. Its kernel V has order8, so |S₂|=512.

Source: Aschbacher–Smith, notation on printed p.440 and J.4.3(1), p.441.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree
noncomputable section
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The actual image of R₂ under the original Ru1 quotient. -/
def Plane.secondImage : Subgroup BinaryLinearThree.Group :=
  (p.R₂.subgroupOf d.L).map d.ru1.quotientMap

theorem Plane.secondImage_eq : p.secondImage =
    (pCore 2 p.parabolic).map p.parabolicMap := by
  ext a
  constructor
  · rintro ⟨l,hl,rfl⟩
    change (l : G) ∈ p.R₂ at hl
    rw [p.R₂_eq] at hl
    obtain ⟨b,hb,he⟩ := hl
    refine ⟨b,hb,?_⟩
    rw [p.parabolicMap_apply]
    exact congrArg d.ru1.quotientMap (Subtype.ext he)
  · rintro ⟨b,hb,rfl⟩
    refine ⟨⟨b,((p.mem_parabolic _).mp b.property).1⟩,?_,(p.parabolicMap_apply b).symm⟩
    change (b : G) ∈ p.R₂
    rw [p.R₂_eq]
    exact ⟨b,hb,rfl⟩

/-- The source commutator in the original Steinberg coordinates. -/
def Plane.steinbergCommutator : Submodule (ZMod 2) Steinberg :=
  subspaceCommutator S ⊤ p.secondImage

/-- The quotient-image description of the original commutator space. -/
theorem Plane.steinbergCommutator_eq_image : p.steinbergCommutator =
    subspaceCommutator S ⊤ p.secondImage := by rfl

theorem Plane.steinbergCommutator_eq : p.steinbergCommutator =
    subspaceCommutator (S.comp d.ru1.quotientMap) ⊤ (p.R₂.subgroupOf d.L) := by
  have h := subspaceCommutator_map_embedding (S.comp d.ru1.quotientMap) S
    d.ru1.quotientMap (LinearMap.id : Steinberg →ₗ[ZMod 2] Steinberg)
    (fun _ _ => rfl) (p.R₂.subgroupOf d.L) ⊤
  simpa only [Plane.steinbergCommutator,Plane.secondImage,Submodule.map_id] using h.symm

theorem Plane.finrank_steinbergCommutator :
    Module.finrank (ZMod 2) p.steinbergCommutator = 6 := by
  obtain ⟨g,hg⟩ := p.core_image
  rw [Plane.steinbergCommutator,p.secondImage_eq,hg]
  exact SteinbergStructure.LineRadicalCommutator.finrank_conjugate_commutator g

/-- J.4.3(1), stated with the original quotient map and original R₂ actors. -/
theorem Plane.finrank_R₂_commutator :
    Module.finrank (ZMod 2)
      (subspaceCommutator (S.comp d.ru1.quotientMap) ⊤ (p.R₂.subgroupOf d.L)) = 6 := by
  rw [← p.steinbergCommutator_eq]
  exact p.finrank_steinbergCommutator

theorem Plane.card_steinbergCommutator : Nat.card p.steinbergCommutator = 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    p.finrank_steinbergCommutator]
  rfl

/-- The source S₂ is the full inverse image of [S/V,R₂], as on printed p.440. -/
def Plane.S₂ : Subgroup G :=
  (p.steinbergCommutator.toAddSubgroup.toSubgroup.comap d.ru1.steinberg.coordinates).map
    d.toTypeRuSetup.S.subtype

theorem Plane.S₂_le_S : p.S₂ ≤ d.toTypeRuSetup.S := map_subtype_le _

theorem Plane.mem_S₂ (s : d.toTypeRuSetup.S) :
    (s : G) ∈ p.S₂ ↔ (d.ru1.steinberg.coordinates s).toAdd ∈ p.steinbergCommutator := by
  change (s : G) ∈ Subgroup.map _ _ ↔ _
  rw [mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    exact (Subtype.ext he : a=s) ▸ ha
  · intro hs; exact ⟨s,hs,rfl⟩

theorem Plane.V_le_S₂ : d.V ≤ p.S₂ := by
  intro v hv
  have hs := d.ru1.steinberg.kernel_le hv
  apply (p.mem_S₂ ⟨v,hs⟩).mpr
  have hz := (d.ru1.steinberg.coordinates_eq_one_iff ⟨v,hs⟩).mpr hv
  rw [hz]
  exact p.steinbergCommutator.zero_mem

private theorem card_preimage {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (W : Subgroup B) :
    Nat.card (W.comap f) = Nat.card W * Nat.card f.ker := by
  rw [card_eq_card_quotient_mul_card_subgroup (f.ker.subgroupOf (W.comap f)),
    card_quotient_subgroupOf_comap_eq f hf W,
    Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap f W)).toEquiv]

theorem Plane.card_S₂ : Nat.card p.S₂ = 512 := by
  have hk : Nat.card d.ru1.steinberg.coordinates.ker = 8 := by
    rw [d.ru1.steinberg.kernel_eq,
      Nat.card_congr (subgroupOfEquivOfLe d.ru1.steinberg.kernel_le).toEquiv,
      d.ru1.card_V]
  have hW : Nat.card p.steinbergCommutator.toAddSubgroup.toSubgroup = 64 :=
    p.card_steinbergCommutator
  rw [Plane.S₂,card_map_of_injective d.toTypeRuSetup.S.subtype_injective,
    card_preimage _ d.ru1.steinberg.onto,hk,hW]
end
end CFSG.Quasithin.ChapterJ.RuSubgroup
