module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.Reduction
public import Theory.Mathieu.M11.RankOneSolvablePair
public import Theory.Mathieu.M11.Properties.OuterRestriction
public import Theory.Mathieu.M12.ValueBoundParabolics.ExtensionPair
public import Theory.Mathieu.M12.ValueBoundParabolics.Ambient
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuTwo.M23
/-!
# Mathieu normal-component exclusions

Faithful normal M11 and M23 are the whole ambient group. Native Sylow
pairs exclude these groups. The actual M12 automorphism alternatives and
M22 extension pairs handle outer extensions as well. Solvability or the
literal intrinsic quotient orders certify the local subgroups are proper.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterE.Structure.Sporadic
variable {G : Type*} [Group G] [Finite G]

theorem no_m11 (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hc : centralizer (L : Set G) = ⊥)
    (e : L ≃* M11) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  have ht := normal_eq_top_of_inner L hc e m11_automorphism_inner
  let d : G ≃* M11 := topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans e)
  have hn : ¬ Group.IsSolvable M11 := by
    intro h
    let := h
    exact not_solvable_of_normal_simple L ha
      (Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective)
  apply not_minimal_of_model T d
  intro S
  obtain ⟨P,Q,hsp,hsq,hjoin,hp,hq⟩ := M11RankOne.exists_solvable_pair S
  let := hp
  let := hq
  exact not_minimal_of_pair S P Q (proper_of_solvable hn P) (proper_of_solvable hn Q)
    hsp hsq hjoin

private theorem no_symmetricThree_pair (T : Sylow 2 G) (hn : ¬ Group.IsSolvable G)
    (P Q : Subgroup G) (hp : (T : Subgroup G) ≤ P) (hq : (T : Subgroup G) ≤ Q)
    (hjoin : P ⊔ Q = ⊤)
    (ep : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eq : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let := MathieuOne.isSolvable_of_symmetricThree_twoCore_quotient ep
  let := MathieuOne.isSolvable_of_symmetricThree_twoCore_quotient eq
  exact not_minimal_of_pair T P Q (proper_of_solvable hn P) (proper_of_solvable hn Q) hp hq hjoin

theorem no_m12 (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hc : centralizer (L : Set G) = ⊥)
    (e : L ≃* M12) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  have hn := not_solvable_of_normal_simple L ha
  rcases M12SmallPair.ValueBoundParabolics.Ambient.ambient_equiv_alternatives L hc e with
    ⟨_,⟨d⟩⟩ | ⟨d,_⟩
  · obtain ⟨P,Q,hp,hq,hjoin,⟨ep⟩,⟨eq⟩⟩ :=
      M12SmallPair.ValueBoundParabolics.exists_pair_of_equiv d T
    exact no_symmetricThree_pair T hn P Q hp hq hjoin ep eq
  · obtain ⟨P,Q,_,hp,hq,hjoin,⟨ep⟩,⟨eq⟩⟩ :=
      M12SmallPair.ValueBoundParabolics.Extension.exists_pair_of_equiv d T
    exact no_symmetricThree_pair T hn P Q hp hq hjoin ep eq

theorem no_m22 (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hc : centralizer (L : Set G) = ⊥) (hcore : pCore 2 G = ⊥)
    (e : L ≃* M22) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  obtain ⟨d⟩ := M22ValueBound.Concrete.nonempty_innerCompatiblePair L hc e T
  have hl : 443520 ≤ Nat.card G := by
    have h := Nat.card_le_card_of_injective L.subtype L.subtype_injective
    rwa [Nat.card_congr e.toEquiv,m22_order] at h
  have hs5 : Nat.card (Equiv.Perm (Fin 5)) < Nat.card G := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
    omega
  have hs3 : Nat.card (Equiv.Perm (Fin 3)) < Nat.card G := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
    omega
  exact not_minimal_of_pair T d.first d.second
    (proper_of_core_quotient hcore _ d.firstQuotient hs5)
    (proper_of_core_quotient hcore _ d.secondQuotient hs3)
    d.sylow_le_first d.sylow_le_second d.generate

theorem no_m23 (T : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (hc : centralizer (L : Set G) = ⊥) (e : L ≃* M23) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  have ht := normal_eq_top_of_inner L hc e m23_conj_surjective
  let d : G ≃* M23 := topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans e)
  open M23Geometry in
  let U : Sylow 2 heptadStabilizer := default
  open M23Geometry in
  have hi : ¬ 2 ∣ ((U : Subgroup heptadStabilizer).map heptadStabilizer.subtype).index := by
    rw [index_map_subtype,heptadStabilizer_index]
    exact Nat.prime_two.not_dvd_mul U.not_dvd_index (by decide)
  open M23Geometry in
  let S : Sylow 2 M23 := (U.isPGroup'.map heptadStabilizer.subtype).toSylow hi
  obtain ⟨a,ha⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 23) (by norm_num)
  have hsp : (S : Subgroup M23) ≤ MulAction.stabilizer M23 a := fun x hx => ha ⟨x,hx⟩
  let := m23_isPretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 (9 : Fin 23) a
  let ep : M22 ≃* MulAction.stabilizer M23 a :=
    m23EquivM22PointStabilizer.trans (MulAction.stabilizerEquivStabilizer hg.symm)
  have hp : Nat.card (MulAction.stabilizer M23 a) = 443520 :=
    (Nat.card_congr ep.toEquiv).symm.trans m22_order
  have hproper : MulAction.stabilizer M23 a ≠ ⊤ := by
    intro he
    have hcard := Nat.card_congr ((MulEquiv.subgroupCongr he).trans topEquiv).toEquiv
    rw [hp,m23_order] at hcard
    contradiction
  open M23Geometry in
  have hjoin : heptadStabilizer ⊔ MulAction.stabilizer M23 a = ⊤ := by
    apply heptadStabilizer_isCoatom.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hh := card_le_of_le (show MulAction.stabilizer M23 a ≤ heptadStabilizer from he ▸ le_sup_right)
    rw [heptadStabilizer_card,hp] at hh
    omega
  open M23Geometry in
  exact not_minimal_of_marked_pair T d S heptadStabilizer (MulAction.stabilizer M23 a)
    heptadStabilizer_isCoatom.1 hproper (map_subtype_le _) hsp hjoin
end CFSG.Quasithin.ChapterE.Structure.Sporadic
