module
public import Glauberman.MaximumAbelianReplacement
public import Theory.GroupTheory.SmallMoverFamily
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Sharp bounds on the larger invariant-kernel omega

For the maximum abelian subgroup selected in Niles 7.5, the intersections
with Q and N-alpha agree. Maximum abelian order bounds the fixed index on
Omega1 Z(N-alpha) by |S:Q|. The smaller core omega supplies the reverse
bound. A residual conjugate selected to generate H with S then gives
L=<A,A^x>, with LQ=H and fixed index at most |S:Q| squared on the larger
omega. The full normal kernel and all fixed vectors remain in these indices.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.6,
printed pp.61-62, the count preceding assertion (2).
-/

public section
open Subgroup
namespace Glauberman
variable {H : Type*} [Group H] [Finite H]

theorem maximum_abelian_kernel_omega_index
    (S : Sylow 2 H) (N : Subgroup H)
    (hNQ : N ≤ pCore 2 H)
    (hVN : omegaCenterIn (pCore 2 H) ≤ omegaCenterIn N)
    (q : ℕ) (hidx : (pCore 2 H).relIndex (S : Subgroup H) = q)
    (hlower : ∀ A : Subgroup H, ¬ A ≤ pCore 2 H →
      q ≤ (centralizer (A : Set H)).relIndex (omegaCenterIn (pCore 2 H)))
    (A : Subgroup H) (hA : A ∈ thompsonAbelianSubgroups (S : Subgroup H))
    (hout : ¬ A ≤ pCore 2 H) (hAN : A ⊓ pCore 2 H = A ⊓ N) :
    (centralizer (A : Set H)).relIndex (omegaCenterIn N) = q := by
  have hWN : omegaCenterIn N ≤ N := fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hWc : omegaCenterIn N ≤ centralizer (N : Set H) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hu := maximum_abelian_offender_bound hA
    (hWN.trans (hNQ.trans (pCore_isPGroup.le_sylow_of_normal S))) hWN
    (inferInstance : IsMulCommutative (omegaCenterIn N)) hWc
  rw [inf_relIndex_left,←inf_relIndex_left A N,←hAN,inf_relIndex_left] at hu
  apply le_antisymm (hu.trans ?_) ((hlower A hout).trans ?_)
  · exact ((pCore 2 H).relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans_eq hidx
  · exact (centralizer (A : Set H)).relIndex_le_of_le_right hVN index_ne_zero_of_finite

omit [Finite H] in
private theorem centralizer_join (A B : Subgroup H) :
    centralizer ((A ⊔ B : Subgroup H) : Set H) = centralizer (A : Set H) ⊓ centralizer (B : Set H) := by
  apply le_antisymm (le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
    (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

omit [Finite H] in
theorem selected_pair_fixed_index_bound
    (S Q W A : Subgroup H) [Q.Normal] [W.Normal]
    (hAQ : A ⊔ Q = S) (x : H)
    (hpair : S ⊔ S.map (MulAut.conj x).toMonoidHom = ⊤)
    (q : ℕ) (hidx : (centralizer (A : Set H)).relIndex W = q) :
    (A ⊔ A.map (MulAut.conj x).toMonoidHom) ⊔ Q = ⊤ ∧
      (centralizer ((A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup H) : Set H)).relIndex W ≤ q^2 := by
  have hQx : Q.map (MulAut.conj x).toMonoidHom = Q :=
    normal_iff_map_conj_eq.mp inferInstance x
  have hWx : W.map (MulAut.conj x).toMonoidHom = W :=
    normal_iff_map_conj_eq.mp inferInstance x
  have hAx := SmallMover.centralizer_index_map (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective W A
  rw [hWx,hidx] at hAx
  constructor
  · rw [←hAQ,Subgroup.map_sup,hQx] at hpair
    simpa only [sup_assoc,sup_left_comm,sup_comm,sup_idem,sup_left_idem] using hpair
  · rw [centralizer_join]
    exact (relIndex_inf_le).trans_eq (by rw [hidx,hAx]; exact (pow_two q).symm)

end Glauberman
