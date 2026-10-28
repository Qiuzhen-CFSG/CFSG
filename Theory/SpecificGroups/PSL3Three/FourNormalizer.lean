module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer.Marked

/-!
# Arbitrary four-subgroup normalizers in PSL₃(3)

Simultaneous diagonalization transports the computed diagonal normalizer S₄
and self-centralizer to every elementary four-subgroup. The final statements
use the actual projective matrix group, and arbitrary carriers equivalent to
that group. Every transport uses the literal subgroup map of the equivalence.

Source: Aschbacher--Smith, quasithin manuscript, Lemma 2.5.8(5), pp.556--557.
-/

public section
namespace Matrix.PSL3Three
open Subgroup FourGeometry

private theorem normalizer_equiv_of_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (B : Subgroup H) (h : A.map e.toMonoidHom = B) :
    Nonempty (normalizer (A : Set G) ≃* normalizer (B : Set H)) := by
  exact ⟨(MulEquiv.subgroupMap e (normalizer (A : Set G))).trans
    (MulEquiv.subgroupCongr (by
      change (normalizer (A : Set G)).map e.toMonoidHom = _
      rw [map_equiv_normalizer_eq, h]))⟩

private theorem centralizer_eq_of_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (B : Subgroup H) (h : A.map e.toMonoidHom = B)
    (hB : centralizer (B : Set H) = B) : centralizer (A : Set G) = A := by
  have hh : (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set H) := by
    apply le_antisymm (map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hh, h, hB]

/-- Every elementary four-subgroup of SL₃(3) has normalizer S₄. -/
theorem normalizer_four_nonempty_equiv_SL (F : Subgroup SL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nonempty (normalizer (F : Set SL) ≃* Equiv.Perm (Fin 4)) := by
  let : IsElementaryAbelian 2 F := hF
  obtain ⟨g, hg⟩ := exists_conj_diagonalFour F hc
  obtain ⟨e⟩ := normalizer_equiv_of_map (MulAut.conj g) F diagonalFour hg
  exact ⟨e.trans diagonalFourNormalizerEquiv⟩

/-- Every elementary four-subgroup of SL₃(3) is its own full centralizer. -/
theorem centralizer_four_SL (F : Subgroup SL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    centralizer (F : Set SL) = F := by
  let : IsElementaryAbelian 2 F := hF
  obtain ⟨g, hg⟩ := exists_conj_diagonalFour F hc
  exact centralizer_eq_of_map (MulAut.conj g) F diagonalFour hg centralizer_diagonalFour

/-- Every elementary four-subgroup of the actual PSL₃(3) has normalizer S₄. -/
theorem normalizer_four_nonempty_equiv (F : Subgroup PSL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nonempty (normalizer (F : Set PSL) ≃* Equiv.Perm (Fin 4)) := by
  let : IsElementaryAbelian 2 F := hF
  let A := F.map equiv.symm.toMonoidHom
  obtain ⟨e⟩ := normalizer_equiv_of_map equiv.symm F A rfl
  obtain ⟨f⟩ := normalizer_four_nonempty_equiv_SL A
    (IsElementaryAbelian.map equiv.symm.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective equiv.symm.injective, hc])
  exact ⟨e.trans f⟩

/-- Every elementary four-subgroup of the actual PSL₃(3) is self-centralizing. -/
theorem centralizer_four (F : Subgroup PSL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    centralizer (F : Set PSL) = F := by
  let : IsElementaryAbelian 2 F := hF
  let A := F.map equiv.symm.toMonoidHom
  exact centralizer_eq_of_map equiv.symm F A rfl
    (centralizer_four_SL A (IsElementaryAbelian.map equiv.symm.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective equiv.symm.injective, hc]))

/-- The normalizer calculation on a carrier identified with the literal PSL₃(3). -/
theorem normalizer_four_nonempty_equiv_of_equiv {K : Type*} [Group K]
    (e : K ≃* PSL) (F : Subgroup K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nonempty (normalizer (F : Set K) ≃* Equiv.Perm (Fin 4)) := by
  let : IsElementaryAbelian 2 F := hF
  obtain ⟨f⟩ := normalizer_equiv_of_map e F (F.map e.toMonoidHom) rfl
  obtain ⟨g⟩ := normalizer_four_nonempty_equiv (F.map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])
  exact ⟨f.trans g⟩

/-- The self-centralizer calculation on a carrier identified with PSL₃(3). -/
theorem centralizer_four_of_equiv {K : Type*} [Group K]
    (e : K ≃* PSL) (F : Subgroup K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    centralizer (F : Set K) = F := by
  let : IsElementaryAbelian 2 F := hF
  exact centralizer_eq_of_map e F (F.map e.toMonoidHom) rfl
    (centralizer_four (F.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hc]))

end Matrix.PSL3Three
