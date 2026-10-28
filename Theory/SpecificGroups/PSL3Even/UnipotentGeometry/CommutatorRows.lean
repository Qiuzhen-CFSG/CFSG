module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.GroupTheory.TwoPlaneCover
/-! # Commutator rows in the binary linear Sylow group
A noncentral involution centralizes one elementary root plane. Its index
and commutator row have order q; elementary central covers preserve the
centralizer and make the row disjoint from the literal covering kernel.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Matrix.PSL3Even.UnipotentGeometry
variable {F:Type*} [Field F]
theorem planes_generate : V₁ F⊔V₂ F=⊤ := by
  apply top_unique
  intro a _
  have h:a=(⟨a.x,0,a.c-a.x*a.y⟩:U F)*(⟨0,a.y,0⟩:U F):=by
    apply U.ext <;> simp
  rw [h]
  exact mul_mem_sup (by simp) (by simp)
theorem class_two : _root_.commutator (U F)≤center (U F) := by
  rw [←Z_eq_center,←ker_abelianization]
  apply commutator_le.mpr
  intro a _ b _
  change (abelianization F) ⁅a,b⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _
theorem center_le_planes : center (U F)≤V₁ F⊓V₂ F := by
  rw [←Z_eq_center]
  intro a ha
  exact ⟨(mem_V₁ F a).mpr ((mem_Z F a).mp ha).2,
    (mem_V₂ F a).mpr ((mem_Z F a).mp ha).1⟩
theorem involution_centralizer_index [Finite F] [CharP F 2]
    (a:U F) (ha:a^2=1) (hz:a∉center (U F)) :
    (centralizer ({a}:Set (U F))).index=Nat.card F := by
  have hz':a∉Z F:=by rwa [Z_eq_center]
  have hcard:Nat.card (centralizer ({a}:Set (U F)))=Nat.card F^2:=by
    rcases centralizer_involution F a ha hz' with h|h
    · rw [h,card_V₁]
    · rw [h,card_V₂]
  have hc:0<Nat.card F^2:=pow_pos Nat.card_pos 2
  apply Nat.eq_of_mul_eq_mul_left hc
  rw [←hcard,Subgroup.card_mul_index,card_U,hcard]
  ring

variable {E:Type*} [Group E] [Finite E]
/-- The source central-cover calculation keeps the exact marked kernel. -/
theorem cover_involution_commutator [Finite F] [CharP F 2]
    (f:E→*U F) (hf:Function.Surjective f)
    [IsElementaryAbelian 2 ((V₁ F).comap f)]
    [IsElementaryAbelian 2 ((V₂ F).comap f)]
    (a:E) (ha:a^2=1) (hz:a∉center E) :
    _root_.commutator E≤center E ∧
      centralizer ({a}:Set E)=(centralizer ({f a}:Set (U F))).comap f ∧
      Nat.card (⁅zpowers a,⊤⁆:Subgroup E)=Nat.card F ∧
      Disjoint (⁅zpowers a,⊤⁆:Subgroup E) f.ker := by
  have hz:f a∉center _:=by
    intro hh
    apply hz
    rw [Subgroup.TwoPlaneCover.center_eq_comap f hf (V₁ F) (V₂ F)
      planes_generate center_le_planes]
    exact hh
  have hc:=Subgroup.TwoPlaneCover.class_two f hf (V₁ F) (V₂ F)
    planes_generate center_le_planes class_two
  have hp:(f a)^2=1:=by rw [←map_pow,ha,map_one]
  have he:centralizer ({a}:Set E)=(centralizer ({f a}:Set (U F))).comap f:=by
    have hplanes:=centralizer_involution F (f a) hp (by rwa [Z_eq_center])
    rcases hplanes with h|h
    all_goals
      have hi:IsMulCommutative ((centralizer ({f a}:Set (U F))).comap f):=by
        rw [h];infer_instance
      let :=hi
      exact Subgroup.TwoPlaneCover.centralizer_eq_comap f a
  exact ⟨hc,he,(Subgroup.TwoPlaneCover.commutator_card f hf hc a he).trans
    (involution_centralizer_index (f a) hp hz),Subgroup.TwoPlaneCover.commutator_disjoint_kernel f hc a he⟩
end Matrix.PSL3Even.UnipotentGeometry

