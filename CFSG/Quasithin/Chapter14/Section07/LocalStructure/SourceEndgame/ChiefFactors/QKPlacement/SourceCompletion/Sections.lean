module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# Source subgroup intervals on the actual S/V action

Images of L₁-normalized subgroups define invariant subspaces of the literal
quotient S/V. A genuine equivariant homomorphism on A with exact kernel B
transports an irreducible noncentral module to the interval between the
images of B and A. The proof pulls any intermediate invariant subspace back
to A and maps it to the irreducible target, so it requires no inclusion of
S in the actor L₁. Actual commutator containments supply the central gaps.

Source application: the three noncentral layers in 14.7.71–72, printed
pp.1075–1076, on the original L₁ action marked by qL.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open SteinbergRecognition.ModuleRecognition
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  [(V.subgroupOf (SteinbergRecognition.S F L)).Normal]
  [IsElementaryAbelian 2 (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))]

abbrev Carrier := Additive (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))

def sourceActor : F.Li L 1 →* BinaryLinearThree.Group :=
  d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left))

abbrev sourceRepresentation (a : QuotientAction d) := a.representation.comp (sourceActor d)

abbrev subgroupImage (A : Subgroup G) : Submodule (ZMod 2) (Carrier (F := F) (L := L)) :=
  AddSubgroup.toZModSubmodule 2 ((A.subgroupOf (SteinbergRecognition.S F L)).map quotientCoordinates).toAddSubgroup'

omit [Finite G] in
theorem mem_subgroupImage (A : Subgroup G) (v : Carrier (F := F) (L := L)) :
    v ∈ subgroupImage A ↔ ∃ s : SteinbergRecognition.S F L, (s : G) ∈ A ∧ (quotientCoordinates s).toAdd = v := by
  change Multiplicative.ofAdd v ∈ (A.subgroupOf (SteinbergRecognition.S F L)).map quotientCoordinates ↔ _
  constructor
  · rintro ⟨s, hs, he⟩; exact ⟨s, hs, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨s, hs, he⟩; exact ⟨s, hs, Multiplicative.toAdd.injective he⟩

def imageNode (a : QuotientAction d) (A : Subgroup G)
    (hA : F.Li L 1 ≤ normalizer (A : Set G)) : Subrepresentation (sourceRepresentation d a) where
  toSubmodule := subgroupImage A
  apply_mem_toSubmodule l v hv := by
    obtain ⟨s, hs, rfl⟩ := (mem_subgroupImage A v).mp hv
    change a.representation (d.qL (inclusion ((F.Li_le L 1).trans inf_le_left) l)) _ ∈ _
    rw [← a.equivariant]
    exact (mem_subgroupImage A _).mpr ⟨_, (mem_normalizer_iff.mp (hA l.property) s).mp hs, rfl⟩


theorem imageNode_mono (a : QuotientAction d) {A B : Subgroup G}
    {hA : F.Li L 1 ≤ normalizer (A : Set G)} {hB : F.Li L 1 ≤ normalizer (B : Set G)}
    (hAB : A ≤ B) : imageNode d a A hA ≤ imageNode d a B hB := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := (mem_subgroupImage A v).mp hv
  exact (mem_subgroupImage B _).mpr ⟨s, hAB hs, rfl⟩

theorem imageNode_central (a : QuotientAction d) {A B : Subgroup G}
    {hA : F.Li L 1 ≤ normalizer (A : Set G)} {hB : F.Li L 1 ≤ normalizer (B : Set G)}
    (hcomm : ⁅F.Li L 1, B⁆ ≤ A) : Central (imageNode d a A hA) (imageNode d a B hB) := by
  intro l v hv
  obtain ⟨s, hs, rfl⟩ := (mem_subgroupImage B v).mp hv
  let c : SteinbergRecognition.S F L := ⟨(l:G) * s * (l:G)⁻¹,
    (mem_normalizer_iff.mp (L_normalizes_S ((F.Li_le L 1 l.property).1)) s).mp s.property⟩
  have hm : (c * s⁻¹ : SteinbergRecognition.S F L).val ∈ A :=
    hcomm (commutator_mem_commutator l.property hs)
  refine (mem_subgroupImage A _).mpr ⟨c * s⁻¹, hm, ?_⟩
  rw [map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  exact congrArg (fun z => z - (quotientCoordinates s).toAdd)
    (a.equivariant (inclusion ((F.Li_le L 1).trans inf_le_left) l) s)

private theorem imageNode_mem_iff (a : QuotientAction d) (A : Subgroup G)
    (hA : F.Li L 1 ≤ normalizer (A : Set G)) (hVA : V ≤ A) (s : SteinbergRecognition.S F L) :
    (quotientCoordinates s).toAdd ∈ imageNode d a A hA ↔ (s : G) ∈ A := by
  constructor
  · intro hs
    obtain ⟨t, ht, he⟩ := (mem_subgroupImage A _).mp hs
    have hk : (s / t : SteinbergRecognition.S F L).val ∈ V := (QuotientGroup.eq_iff_div_mem (N := V.subgroupOf (SteinbergRecognition.S F L))).mp he.symm
    simpa using A.mul_mem (hVA hk) ht
  · intro hs
    exact (mem_subgroupImage A _).mpr ⟨s, hs, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem imageNode_chief (a : QuotientAction d) (A B : Subgroup G)
    (hA : F.Li L 1 ≤ normalizer (A : Set G))
    (hB : F.Li L 1 ≤ normalizer (B : Set G))
    (hAS : A ≤ SteinbergRecognition.S F L) (hBA : B ≤ A) (hVB : V ≤ B)
    (τ : Representation (ZMod 2) (F.Li L 1) M) [IsIrreducible τ]
    (f : A →* Multiplicative M) (hf : Function.Surjective f)
    (hk : ∀ x : A, f x = 1 ↔ (x : G) ∈ B)
    (heq : ∀ (l : F.Li L 1) (x : A),
      (f ⟨(l:G)*x*(l:G)⁻¹, (mem_normalizer_iff.mp (hA l.property) x).mp x.property⟩).toAdd =
        τ l (f x).toAdd)
    (hnt : ∃ l v, τ l v ≠ v) :
    imageNode d a B hB ⋖ imageNode d a A hA ∧
      ¬ Central (imageNode d a B hB) (imageNode d a A hA) := by
  have hle := imageNode_mono d a (hA := hB) (hB := hA) hBA
  have hnon : ¬ Central (imageNode d a B hB) (imageNode d a A hA) := by
    intro hcentral
    obtain ⟨l, v, hv⟩ := hnt
    obtain ⟨x, hx⟩ := hf (Multiplicative.ofAdd v)
    let s : SteinbergRecognition.S F L := ⟨x, hAS x.property⟩
    let y : A := ⟨(l:G)*x*(l:G)⁻¹, (mem_normalizer_iff.mp (hA l.property) x).mp x.property⟩
    have hm := hcentral l (quotientCoordinates s).toAdd
      ((mem_subgroupImage A _).mpr ⟨s, x.property, rfl⟩)
    have hyx : ((y * x⁻¹ : A) : G) ∈ B := by
      apply (imageNode_mem_iff d a B hB hVB ⟨y*x⁻¹, hAS (A.mul_mem y.property (A.inv_mem x.property))⟩).mp
      have he : (quotientCoordinates (⟨y*x⁻¹, hAS (A.mul_mem y.property (A.inv_mem x.property))⟩ : SteinbergRecognition.S F L)).toAdd =
          sourceRepresentation d a l (quotientCoordinates s).toAdd - (quotientCoordinates s).toAdd := by
        change (quotientCoordinates (⟨y,hAS y.property⟩ * s⁻¹)).toAdd = _
        rw [map_mul, map_inv]
        simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
        exact congrArg (fun z => z - (quotientCoordinates s).toAdd)
          (a.equivariant (inclusion ((F.Li_le L 1).trans inf_le_left) l) s)
      exact he.symm ▸ hm
    have hf0 := (hk (y*x⁻¹)).mpr hyx
    rw [map_mul, map_inv] at hf0
    have hy : f y = f x := mul_inv_eq_one.mp hf0
    apply hv
    have hx' : (f x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact (heq l x).symm.trans (congrArg Multiplicative.toAdd hy)
  refine ⟨⟨lt_of_le_of_ne hle ?_, ?_⟩, hnon⟩
  · intro he
    apply hnon
    rw [he]
    intro l v hv
    exact (imageNode d a A hA).toSubmodule.sub_mem
      ((imageNode d a A hA).apply_mem_toSubmodule l hv) hv
  · intro P hBP hPA
    let D : Subgroup A := ((P.toSubmodule.toAddSubgroup.toSubgroup).comap
      (quotientCoordinates.comp (inclusion hAS)))
    let J : Subrepresentation τ := {
      toSubmodule := AddSubgroup.toZModSubmodule 2 (D.map f).toAddSubgroup'
      apply_mem_toSubmodule l v hv := by
        obtain ⟨x, hx, he⟩ := hv
        let y : A := ⟨(l:G)*x*(l:G)⁻¹, (mem_normalizer_iff.mp (hA l.property) x).mp x.property⟩
        have hy : y ∈ D := by
          change (quotientCoordinates (inclusion hAS y)).toAdd ∈ P
          have he := a.equivariant (inclusion ((F.Li_le L 1).trans inf_le_left) l) (inclusion hAS x)
          exact he.symm ▸ P.apply_mem_toSubmodule l hx
        exact ⟨y, hy, Multiplicative.toAdd.injective ((heq l x).trans (congrArg (τ l) (congrArg Multiplicative.toAdd he)))⟩ }
    rcases eq_bot_or_eq_top J with hJ | hJ
    · have hPB : P ≤ imageNode d a B hB := by
        intro v hv
        obtain ⟨s, hs, rfl⟩ := (mem_subgroupImage A v).mp (hPA.le hv)
        let x : A := ⟨s, hs⟩
        have hm : (f x).toAdd ∈ J := ⟨x, hv, rfl⟩
        have hz : f x = 1 := by
          apply Multiplicative.toAdd.injective
          have hh : J.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hJ
          exact (Submodule.mem_bot (R := ZMod 2)).mp (hh ▸ hm)
        exact (mem_subgroupImage B _).mpr ⟨s, (hk x).mp hz, rfl⟩
      exact hBP.not_ge hPB
    · have hAP : imageNode d a A hA ≤ P := by
        intro v hv
        obtain ⟨s, hs, rfl⟩ := (mem_subgroupImage A v).mp hv
        let x : A := ⟨s, hs⟩
        have hm : (f x).toAdd ∈ J := hJ ▸ Submodule.mem_top
        obtain ⟨y, hy, he⟩ := hm
        have hkxy : ((x / y : A) : G) ∈ B := (hk _).mp (by rw [map_div, he]; exact div_self' _)
        have hpB : (quotientCoordinates (inclusion hAS (x/y))).toAdd ∈ P :=
          hBP.le ((mem_subgroupImage B _).mpr ⟨_, hkxy, rfl⟩)
        have hp := P.toSubmodule.add_mem hpB hy
        have he : (quotientCoordinates (inclusion hAS (x/y))).toAdd +
            (quotientCoordinates (inclusion hAS y)).toAdd = (quotientCoordinates s).toAdd := by
          rw [← toAdd_mul, ← map_mul, ← map_mul]
          simp only [div_mul_cancel]
          rfl
        exact he ▸ hp
      exact hPA.not_ge hAP

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
