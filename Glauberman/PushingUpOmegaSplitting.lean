module
public import Glauberman.QuadraticOffenderSelection
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SubgroupSectionConjugation
public import Theory.GroupTheory.RankOneInvariantKernelOrbit
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The enlarged central omega layer in Niles Lemma7.6

For the maximum abelian subgroup selected in Lemma7.5, its intersection with
N_alpha equals its intersection with O2(H). Maximal abelian order therefore
bounds the fixed index on W=Omega1 Z(N_alpha) by four. The conjugate actor has
the same bound, so their join has fixed index at most sixteen. The natural
module V=Omega1 Z(O2(H)) attains sixteen, forcing W=V C_W(L). In particular
[W,L]=[V,L]. All subgroups and fixed indices remain in the original ambient
group. The natural-module lower bound is the separate source2.9 input.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma7.6, printed pp.61–62.
-/

public section
open Subgroup
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

/-- Equal fixed indices force a fixed-point supplement in an abelian layer. -/
theorem abelian_eq_sup_fixed_of_relIndex (V W L : Subgroup G)
    (hVW : V ≤ W) (hc : IsMulCommutative W)
    (hi : (centralizer (L : Set G)).relIndex W ≤
      (centralizer (L : Set G)).relIndex V) :
    W = V ⊔ (W ⊓ centralizer (L : Set G)) := by
  let C := W ⊓ centralizer (L : Set G)
  have hC : C ≤ W := inf_le_left
  let _ := hc
  have hn : C ≤ normalizer (V : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx y hy
    exact setLike_mul_comm (hVW hy) hx.1
  have hfix : C.relIndex V = (centralizer (L : Set G)).relIndex V := by
    rw [relIndex,relIndex]
    congr 1
    ext x
    exact ⟨fun h => h.2,fun h => ⟨hVW x.property,h⟩⟩
  have hprod := relIndex_mul_relIndex C (V ⊔ C) W le_sup_right (sup_le hVW hC)
  rw [relIndex_sup_of_normalizes V C hn,hfix] at hprod
  change (centralizer (L : Set G)).relIndex V * (V ⊔ C).relIndex W =
    (W ⊓ centralizer (L : Set G)).relIndex W at hprod
  rw [inf_relIndex_left] at hprod
  have hp : 0 < (centralizer (L : Set G)).relIndex V :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hj : (V ⊔ C).relIndex W = 1 := by
    have hjp : 0 < (V ⊔ C).relIndex W := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hle : (centralizer (L : Set G)).relIndex V * (V ⊔ C).relIndex W ≤
        (centralizer (L : Set G)).relIndex V * 1 := by simpa only [mul_one,hprod] using hi
    have hh := Nat.le_of_mul_le_mul_left hle hp
    omega
  exact le_antisymm (relIndex_eq_one.mp hj) (sup_le hVW hC)

/-- Two conjugate actor bounds give the source W=V C_W(L) identity. -/
theorem abelian_eq_sup_fixed_of_conjugate_bounds
    (V W A : Subgroup G) [W.Normal] (g : G) (d : ℕ)
    (hVW : V ≤ W) (hc : IsMulCommutative W)
    (hA : (W ⊓ centralizer (A : Set G)).relIndex W ≤ d)
    (hV : d*d ≤ (centralizer ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).relIndex V) :
    W = V ⊔ (W ⊓ centralizer ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  apply abelian_eq_sup_fixed_of_relIndex V W _ hVW hc
  have hcj := Theory.GroupTheory.inf_centralizer_conjugate W A g
  have hwj : W.map (MulAut.conj g).toMonoidHom = W :=
    normal_iff_map_conj_eq.mp (inferInstance : W.Normal) g
  have hidx := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (W ⊓ centralizer (A : Set G)) W
    (MulAut.conj g).injective
  rw [hcj,hwj] at hidx
  have hle : ((W ⊓ centralizer (A : Set G)) ⊓
      (W ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G))).relIndex W ≤
      d*d := relIndex_inf_le.trans (Nat.mul_le_mul hA (hidx.trans_le hA))
  have he : (W ⊓ centralizer (A : Set G)) ⊓
      (W ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)) =
      W ⊓ centralizer ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [centralizer_join]
    exact inf_inf_inf_comm W _ W _ |>.trans (by rw [inf_idem])
  rw [he,inf_relIndex_left] at hle
  exact hle.trans hV

/-- In the selected-intersection situation of Niles7.5, the actual enlarged
omega layer still has fixed index at most the quotient order. -/
theorem maximum_abelian_omega_fixed_bound
    (S Q N A : Subgroup G)
    (hA : A ∈ thompsonAbelianSubgroups S) (hNS : N ≤ S)
    (hinter : A ⊓ Q = A ⊓ N) (d : ℕ) (hidx : Q.relIndex A ≤ d) :
    (omegaCenterIn N ⊓ centralizer (A : Set G)).relIndex (omegaCenterIn N) ≤ d := by
  have hW : omegaCenterIn N ≤ N := fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hc : omegaCenterIn N ≤ centralizer (N : Set G) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hb := maximum_abelian_offender_bound hA (hW.trans hNS) hW inferInstance hc
  have he : N.relIndex A = Q.relIndex A := by
    rw [← inf_relIndex_left A N,← inf_relIndex_left A Q,hinter]
  exact hb.trans (he.trans_le hidx)

/-- Literal enlarged-omega splitting for the original selected A. The index
sixteen on V is precisely the independent natural-module input. -/
theorem omega_eq_coreOmega_sup_fixed
    (S Q N A : Subgroup G) [N.Normal]
    (hA : A ∈ thompsonAbelianSubgroups S) (hNS : N ≤ S) (hNQ : N ≤ Q)
    (hVN : omegaCenterIn Q ≤ N) (hinter : A ⊓ Q = A ⊓ N)
    (hidx : Q.relIndex A ≤ 4) (g : G)
    (hV : 16 ≤ (centralizer
      ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).relIndex
        (omegaCenterIn Q)) :
    omegaCenterIn N = omegaCenterIn Q ⊔ (omegaCenterIn N ⊓ centralizer
      ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  have hVW : omegaCenterIn Q ≤ omegaCenterIn N := by
    intro x hx
    obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hVN hx,centralizer_le hNQ hc,hp⟩
  have hWN : (omegaCenterIn N).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    calc
      ⊤ = normalizer (N : Set G) := (Subgroup.normalizer_eq_top N).symm
      _ ≤ normalizer (omegaCenterIn N : Set G) := normalizer_le_normalizer_omegaCenterIn N
  exact abelian_eq_sup_fixed_of_conjugate_bounds (omegaCenterIn Q)
    (omegaCenterIn N) A g 4 hVW inferInstance
    (maximum_abelian_omega_fixed_bound S Q N A hA hNS hinter 4 hidx) hV

omit [Finite G] in
/-- Splitting off L-fixed vectors leaves the actual commutator unchanged. -/
theorem commutator_eq_of_abelian_fixed_splitting (V W L : Subgroup G)
    (hc : IsMulCommutative W) (hn : L ≤ normalizer (W : Set G))
    (he : W = V ⊔ (W ⊓ centralizer (L : Set G))) : ⁅W,L⁆ = ⁅V,L⁆ := by
  have hVW : V ≤ W := he ▸ le_sup_left
  have hmW : ⁅V,L⁆ ≤ W :=
    (commutator_mono hVW le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hn)
  let _ := hc
  have hWm : W ≤ normalizer (⁅V,L⁆ : Subgroup G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro w hw m hm
    exact setLike_mul_comm (hmW hm) hw
  apply le_antisymm ?_ (commutator_mono hVW le_rfl)
  calc
    ⁅W,L⁆ = ⁅V ⊔ (W ⊓ centralizer (L : Set G)),L⁆ := congrArg (fun X => ⁅X,L⁆) he
    _ ≤ ⁅V,L⁆ := commutator_sup_le_of_relative_normal W V _ L _ hWm hVW inf_le_left
      le_rfl ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)

end Glauberman
