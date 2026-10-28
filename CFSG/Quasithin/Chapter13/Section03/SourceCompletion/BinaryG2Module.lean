module
public import Theory.Representation.G2BinaryFixedSpaceFamily
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# The binary G₂ model row on the original automizer

The natural six-space marking of a normal G₂(2)′ subgroup embeds the entire
faithful ambient action in the proved full normalizer G₂(2). Equivariant
transport preserves every fixed-space-family equality. The native model
therefore gives parameter two, rank three, and an actor moving three
dimensions. Its actual lift to A supplies an injection of that displacement
space into [V,A], proving the original commutator corank bound.

This discharges B.4.6(3),(9) in the original 13.3.19(2) consumer, without a
family-classification, displacement or involutory-lift premise. The actual
normal subgroup/module marking is the earlier source datum of 13.3.2.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE

section Transport
variable {X U:Type*} [Group X] [Finite X] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  (τ:Representation (ZMod 2) X U)

omit [Finite X] [FiniteDimensional (ZMod 2) U] in
/-- Injective equivariant transport preserves the literal fixed-space family. -/
theorem fixedSpaceFamily_map_binaryG2
    (f:X→*Atlas.G2.Model (ZMod 2)) (hf:Function.Injective f)
    (E:U≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀x v,E (τ x v)=Atlas.G2.Natural.action (ZMod 2) (f x) (E v))
    {A:Subgroup X} {k:ℕ} (hA:A∈fixedSpaceFamily τ k) :
    A.map f∈fixedSpaceFamily Atlas.G2.Natural.BinaryFixedFamily.ρ k := by
  let σ:=Atlas.G2.Natural.BinaryFixedFamily.ρ
  let : IsElementaryAbelian 2 A:=hA.2.1.2
  have hn:A.map f≠⊥ := by
    intro hh
    apply hA.2.1.1
    apply (map_injective hf)
    simpa using hh
  refine ⟨hA.1,⟨hn,IsElementaryAbelian.map f⟩,?_⟩
  intro B hBA hB
  let C:=B.comap f
  have hCA:C≤A := by
    have hh:=Subgroup.comap_mono (f:=f) hBA
    rwa [comap_map_eq_self_of_injective hf] at hh
  have hCmap:C.map f=B := by
    rw [map_comap_eq,inf_eq_right.mpr (hBA.trans (map_le_range _ _))]
  have hidx:C.relIndex A=B.relIndex (A.map f) := by
    rw [←hCmap,relIndex_map_map_of_injective _ _ hf]
  have hfixed:=hA.2.2 C hCA (hidx ▸ hB)
  have hh:=congrArg (fun P:Submodule (ZMod 2) U=>P.map E.toLinearMap) hfixed
  rw [fixedSpace_map_equivariant τ σ f E he,
    fixedSpace_map_equivariant τ σ f E he,hCmap] at hh
  exact hh

omit [Finite X] [FiniteDimensional (ZMod 2) U] in
/-- The native binary row transported through an actual faithful action embedding. -/
theorem binaryG2_family_of_embedding
    (hτ:Function.Injective τ)
    (f:X→*Atlas.G2.Model (ZMod 2)) (hf:Function.Injective f)
    (E:U≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀x v,E (τ x v)=Atlas.G2.Natural.action (ZMod 2) (f x) (E v))
    {A:Subgroup X} {k:ℕ} (hk:2≤k) (hA:A∈fixedSpaceFamily τ k) :
    k=2 ∧ rank A=3 ∧ ∃a∈A,orderOf a=2 ∧ fixedCodim τ (zpowers a)=3 := by
  have hmap:=fixedSpaceFamily_map_binaryG2 τ f hf E he hA
  have hr:=parameter_le_rank_of_mem_fixedSpaceFamily τ hτ hA
  rw [←rank_map_injective f hf A] at hr
  obtain ⟨hk2,hAr,a,ha,ho,hcost⟩:=
    Atlas.G2.Natural.BinaryFixedFamily.family_shape_and_displacement k hk _ hmap.2.1 hr hmap.2.2
  obtain ⟨b,hb,rfl⟩:=ha
  rw [rank_map_injective f hf A] at hAr
  refine ⟨hk2,hAr,b,hb,?_,?_⟩
  · rwa [orderOf_injective f hf] at ho
  · have hh:=fixedCodim_map_equivariant τ Atlas.G2.Natural.BinaryFixedFamily.ρ f E he (zpowers b)
    rw [MonoidHom.map_zpowers] at hh
    exact hh.trans hcost
end Transport

section Ambient
variable {G:Type*} [Group G] [Finite G]

/-- One induced actor moving three dimensions forces the required original
commutator corank bound. This uses its actual lift in A, not an involutory lift. -/
theorem commutator_corank_le_three_of_displacement
    (V A:Subgroup G) [IsElementaryAbelian 2 V]
    (hA:A≤normalizer (V:Set G)) (hV:Nat.card V=64)
    (i:Automizer V) (hi:i∈inducedAutomizer V A)
    (hcost:fixedCodim (automizerRepresentation V) (zpowers i)=3) :
    subgroupCorank V ⁅V,A⁆≤3 := by
  obtain ⟨a,ha,hai⟩:=hi
  let δ:=automizerRepresentation V i-LinearMap.id
  have hdim:Module.finrank (ZMod 2) δ.range=3 := by
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    exact hcost
  let j:δ.range→(⁅V,A⁆:Subgroup G) := fun x=>⟨x.val.toMul,by
    obtain ⟨v,hv⟩:=x.property
    rw [←hv]
    change ((automizerRepresentation V i v-v).toMul:V).val∈⁅V,A⁆
    rw [←hai]
    simp only [toMul_sub,div_eq_mul_inv]
    change a.val*v.toMul.val*a.val⁻¹*(v.toMul.val)⁻¹∈⁅V,A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator ha v.toMul.property⟩
  have hj:Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z:(⁅V,A⁆:Subgroup G)=>(z:G)) h
  have h8:8≤Nat.card (⁅V,A⁆:Subgroup G) := by
    have hh:=Nat.card_le_card_of_injective j hj
    have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=δ.range)
    rw [Nat.card_zmod,hdim] at hc
    simpa only [hc,show (2:ℕ)^3=8 by decide] using hh
  have hle:⁅V,A⁆≤V:=le_normalizer_iff_commutator_le_left.mp hA
  have hh:=relIndex_mul_card_of_le hle
  rw [hV] at hh
  have hidx:⁅V,A⁆.relIndex V≤8 := by nlinarith
  have hl:=Nat.log_mono_right (b:=2) hidx
  exact (show subgroupCorank V ⁅V,A⁆≤Nat.log 2 8 from hl).trans (by decide)
/-- B.4.6(3,9) on the original induced automizer, from the actual
six-dimensional module marking of its normal derived G₂ subgroup. -/
theorem binaryG2_automizer_row
    (V:Subgroup G) [IsElementaryAbelian 2 V]
    (L:Subgroup (Automizer V)) [L.Normal]
    (e:L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:L) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v)) :
    ∀A:Subgroup G,A≤normalizer (V:Set G)→∀k:ℕ,2≤k→
      inducedAutomizer V A∈fixedSpaceFamily (automizerRepresentation V) k→
      k=2 ∧ rank (inducedAutomizer V A)=3 ∧ subgroupCorank V ⁅V,A⁆≤3 := by
  obtain ⟨f,hf,_,hfull⟩:=Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation V) L e E he (automizerRepresentation_injective V)
  have hV:Nat.card V=64 := by
    have hd:Module.finrank (ZMod 2) (Additive V)=6:=
      E.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
    have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
    rw [Nat.card_zmod,hd] at hc
    exact hc
  intro A hA k hk hI
  obtain ⟨hk2,hr,i,hi,_,hc⟩:=binaryG2_family_of_embedding (automizerRepresentation V)
    (automizerRepresentation_injective V) f hf E hfull hk hI
  exact ⟨hk2,hr,commutator_corank_le_three_of_displacement V A hA hV i hi hc⟩

end Ambient
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
