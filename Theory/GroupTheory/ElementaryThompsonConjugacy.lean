module
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Thompson transport through a locally prescribed Sylow subgroup

If P≤T contains an ambient conjugate of J(T), equality of maximum
elementary-abelian orders gives J(P)≤J(T) and contains that conjugate.
Cardinality forces equality. When P is a prescribed Sylow subgroup of H,
a conjugate of J(T) lying in H can first be conjugated into P inside H.
All conjugations and subgroup images remain literal.

Source application: Aschbacher–Smith10.2.9, printed p.751, the passage
from a locally saturated point centralizer to J(C_T(v))=J(T).
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup of T containing a conjugate of J(T) has the same Thompson group. -/
theorem elementaryAbelianMaxJ_eq_of_conjugate_le
    (T P : Subgroup G) (hPT : P ≤ T) (a : MulAut G)
    (ha : (elementaryAbelianMaxJ T).map a.toMonoidHom ≤ P) :
    elementaryAbelianMaxJ P = elementaryAbelianMaxJ T := by
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq P T hPT
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    (T.map a.toMonoidHom) P (by rwa [elementaryAbelianMaxJ_map_equiv])
  have he : elementaryAbelianMaxOrder P = elementaryAbelianMaxOrder T :=
    le_antisymm hsmall.1 ((elementaryAbelianMaxOrder_map_equiv a T) ▸ hlarge.1)
  apply eq_of_le_of_card_ge (hsmall.2 he)
  have hj := hlarge.2 ((elementaryAbelianMaxOrder_map_equiv a T).trans he.symm)
  rw [elementaryAbelianMaxJ_map_equiv] at hj
  have hc := card_le_of_le hj
  rwa [card_map_of_injective (K := elementaryAbelianMaxJ T)
    (f := a.toMonoidHom) a.injective] at hc

/-- Local Sylow saturation transports a conjugate of J(T) in H back to
J(T) itself, provided the prescribed Sylow P lies in T. -/
theorem elementaryAbelianMaxJ_eq_of_sylow_of_conjugate_le
    (T P H : Subgroup G) (hPT : P ≤ T) (hT : IsPGroup 2 T)
    (hs : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = P)
    (a : MulAut G) (ha : (elementaryAbelianMaxJ T).map a.toMonoidHom ≤ H) :
    elementaryAbelianMaxJ P = elementaryAbelianMaxJ T := by
  obtain ⟨S,hS⟩ := hs
  let J := (elementaryAbelianMaxJ T).map a.toMonoidHom
  have hp : IsPGroup 2 (J.subgroupOf H) :=
    ((hT.to_le (sSup_le fun _ hA => hA.1)).map a.toMonoidHom).comap_subtype
  obtain ⟨R,hJR⟩ := hp.exists_le_sylow
  obtain ⟨x,hx⟩ := MulAction.exists_smul_eq H R S
  let b := MulAut.conj (x : G)
  apply elementaryAbelianMaxJ_eq_of_conjugate_le T P hPT (a.trans b)
  change (elementaryAbelianMaxJ T).map (b.toMonoidHom.comp a.toMonoidHom) ≤ P
  rw [←map_map]
  rintro _ ⟨j,hj,rfl⟩
  have hm : (MulAut.conj x) (⟨j,ha hj⟩ : H) ∈ (S : Subgroup H) := by
    rw [←hx]
    exact mem_map_of_mem (MulAut.conj x).toMonoidHom (hJR hj)
  exact hS ▸ mem_map_of_mem H.subtype hm

end Stellmacher
