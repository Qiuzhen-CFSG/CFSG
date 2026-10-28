module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LocalInvolutionResidualSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import Theory.GroupTheory.SylowActionAdjustment
public import Theory.GroupTheory.NormalizerActionSubtype

/-!
# Adjusting the original crossing inside the original Sylow subgroup

The component Sylow is Sylow in C_K(zK), whose conjugation action on its
SL₂(3) residual is surjective. Match the action of an original crossing in
T∩N(R) by an element of that component Sylow. Multiplying by its inverse
preserves membership in N_T(S) outside S and centralizes the actual R.
The crossing is not required to normalize K.
Source: Aschbacher--Smith 2.5.15, printed p.558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z x : G}

theorem local_residual_crossing_adjustment
    (c : MathieuSourceSetup H K M S z)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (zK : K) (hzK : orderOf zK = 2)
    (hzS : (zK : G) ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x ∈ normalizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)) :
    ∃ y : G, y ∈ c.T ∧ y ∉ (S : Subgroup H).map H.subtype ∧
      y ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      y ∈ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  let C := centralizer ({zK} : Set K)
  let R := GLTwoThreeLocal.residual zK
  let A := C.map K.subtype
  let B := R.map K.subtype
  have hCB : A ≤ normalizer (B : Set G) :=
    (map_mono (GLTwoThreeLocal.centralizer_le_normalizer_residual zK)).trans (R.le_normalizer_map K.subtype)
  have hsurj : Function.Surjective (B.normalizerMonoidHom.comp (inclusion hCB)) :=
    normalizer_action_map_subtype_surjective K C R
      (GLTwoThreeLocal.centralizer_le_normalizer_residual zK) hCB
      (linear_three_or_mathieu_local_residual K hK zK hzK).2.2
  obtain ⟨P,hP⟩ := ComponentSelection.MathieuSourceSetup.exists_relative_component_sylow c
  have hPC : (P : Subgroup K) ≤ C := by
    intro p hp
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hpY : p ∈ Y.subgroupOf K := by rw [← hP]; exact hp
    exact hzS.2 p hpY
  let PC := P.subtype hPC
  let eC := C.equivMapOfInjective K.subtype K.subtype_injective
  let PA := PC.mapSurjective (f := eC.toMonoidHom) eC.surjective
  have hPA : (PA : Subgroup A).map A.subtype ≤ Y := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩ := ha
    have hbP : (b : K) ∈ (P : Subgroup K) := hb
    have hbY : (b : K) ∈ Y.subgroupOf K := by rw [← hP]; exact hbP
    exact hbY
  let T' := (c.T : Subgroup G) ⊓ normalizer (B : Set G)
  have hPAT : (PA : Subgroup A).map A.subtype ≤ T' := le_inf
    (hPA.trans c.sylow_lt.le) ((map_subtype_le _).trans hCB)
  obtain ⟨p,hp,hpx⟩ := exists_sylow_adjustment_to_centralizer B A T' hCB inf_le_right
    (c.T.isPGroup'.to_le inf_le_left) PA hPAT hsurj x ⟨hxT,hxR⟩
  have hpY : (p : G) ∈ Y := hPA (mem_map_of_mem A.subtype hp)
  refine ⟨(p : G)⁻¹*x,(c.T : Subgroup G).mul_mem ((c.T : Subgroup G).inv_mem
    (c.sylow_lt.le hpY)) hxT,?_,?_,hpx⟩
  · intro hy
    exact hxS (by simpa only [mul_inv_cancel_left] using Y.mul_mem hpY hy)
  · exact (normalizer (Y : Set G)).mul_mem ((normalizer (Y : Set G)).inv_mem
      (Y.le_normalizer hpY)) hxN
end CFSG.Quasithin.Chapter2.Section05
