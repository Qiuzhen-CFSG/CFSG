module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneCentralizer

/-!
# The original cubic Cartan moves the tensor plane

The pointwise stabilizer of the singular plane in the original tensor
quotient has exponent two. The coordinate kernel is a two-group as well,
so no nonidentity cubic element of the original local orbit centralizes
that plane. An order-three Cartan contained in the old residual therefore
supplies the movement premise in the source overgroup argument.

Source: Aschbacher–Smith9.3.5, combined manuscript, printed pp.733–734.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem coordinates_fixed_of_centralizes_plane (b : localOrbit T L)
    (hb : (b : G) ∈ centralizer (m.tensorPlane : Set G)) :
    ∀ v ∈ m.sectionData.imageSpace m.tensorPlane, Binary.action (m.quotient b) v = v := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := (m.sectionData.mem_imageSpace_iff _ _).mp hv
  have he := m.sectionData.equivariant b a
  have hs : (⟨(b : G)*a*(b : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized b.property) a).mp a.property⟩ : D.fullModule) = a := by
    apply Subtype.ext
    change (b : G)*(a : G)*(b : G)⁻¹ = (a : G)
    rw [←hb a ha,mul_inv_cancel_right]
  rw [hs] at he
  exact he.symm

theorem quotient_first_eq_one_of_centralizes_tensorPlane (b : localOrbit T L)
    (hb : (b : G) ∈ centralizer (m.tensorPlane : Set G)) : (m.quotient b).1 = 1 := by
  obtain ⟨P,hP⟩ := m.exists_tensorLine_coordinates_sylow
  have hf := m.coordinates_fixed_of_centralizes_plane b hb
  rw [m.tensorPlane_coordinates_firstOrbit,hP] at hf
  exact Binary.first_eq_one_of_sylow_plane_fixed P (m.quotient b) hf

theorem quotient_square_eq_one_of_centralizes_tensorPlane (b : localOrbit T L)
    (hb : (b : G) ∈ centralizer (m.tensorPlane : Set G)) : (m.quotient b)^2 = 1 := by
  obtain ⟨P,hP⟩ := m.exists_tensorLine_coordinates_sylow
  have hf := m.coordinates_fixed_of_centralizes_plane b hb
  rw [m.tensorPlane_coordinates_firstOrbit,hP] at hf
  exact Binary.square_eq_one_of_sylow_plane_fixed P (m.quotient b) hf

theorem moves_tensorPlane_of_first_factor (K : Subgroup G) (b : localOrbit T L)
    (hbK : (b : G) ∈ K) (hb : (m.quotient b).1 ≠ 1) :
    ¬ K ≤ centralizer (m.tensorPlane : Set G) :=
  fun hc => hb (m.quotient_first_eq_one_of_centralizes_tensorPlane b (hc hbK))

theorem cubic_moves_tensorPlane (b : localOrbit T L) (hb3 : b^3 = 1) (hb1 : b ≠ 1) :
    (b : G) ∉ centralizer (m.tensorPlane : Set G) := by
  intro hc
  have h2 := m.quotient_square_eq_one_of_centralizes_tensorPlane b hc
  have h3 : (m.quotient b)^3 = 1 := by rw [←map_pow,hb3,map_one]
  have hq : m.quotient b = 1 := by
    have he : (m.quotient b)^3 = (m.quotient b)^2*m.quotient b := pow_succ _ 2
    rw [h3,h2,one_mul] at he
    exact he.symm
  have hbcore : b ∈ pCore 2 (localOrbit T L) := m.kernel_eq ▸ hq
  let c : pCore 2 (localOrbit T L) := ⟨b,hbcore⟩
  have hc3 : c^3 = 1 := Subtype.ext hb3
  have hc1 : c = 1 := by
    apply ((pCore_isPGroup (p := 2) (G := localOrbit T L)).powEquiv
      (by decide : Nat.Coprime 2 3)).injective
    change c^3 = (1 : pCore 2 (localOrbit T L))^3
    rw [hc3,one_pow]
  exact hb1 (congrArg Subtype.val hc1)

theorem moves_tensorPlane_of_cubic_subgroup (K B : Subgroup G)
    (hBK : B ≤ K) (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3) :
    ¬ K ≤ centralizer (m.tensorPlane : Set G) := by
  have hn : B ≠ ⊥ := by
    intro hb
    rw [hb,Subgroup.card_bot] at hB
    omega
  obtain ⟨b,hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  let b0 : localOrbit T L := ⟨b,hBL b.property⟩
  have hb3 : b0^3 = 1 := by
    apply Subtype.ext
    have hp : b^3 = 1 := hB ▸ (pow_card_eq_one' (x := b))
    exact congrArg (fun x : B => (x : G)) hp
  have hb01 : b0 ≠ 1 := by
    intro he
    exact hb1 (Subtype.ext (congrArg (fun x : localOrbit T L => (x : G)) he))
  intro hc
  exact m.cubic_moves_tensorPlane b0 hb3 hb01 (hc (hBK b.property))

/-- The original order-three Cartan inside the old residual supplies source 9.3.5(1). -/
theorem old_residual_moves_tensorPlane_of_cartan (oldH B : Subgroup G)
    (hBK : B ≤ (pResidual 2 oldH).map oldH.subtype)
    (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3) :
    ¬ (pResidual 2 oldH).map oldH.subtype ≤ centralizer (m.tensorPlane : Set G) :=
  m.moves_tensorPlane_of_cubic_subgroup _ B hBK hBL hB

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
