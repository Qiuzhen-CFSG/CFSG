module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SylowModels
public import Theory.Mathieu.M11.Properties.SylowFixedOddCore
public import Theory.GroupTheory.SemidihedralAut
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# Mathieu exclusions for the actual moved component

The Sylow automorphism stabilizers in M₁₁, M₁₂ and M₂₄ are two-groups.
For M₁₁ and M₁₂, restriction to a Sylow subgroup has two-group image and
pointwise kernel. For M₂₄, the checked self-normalizer calculation and
outer two-group bound give the same conclusion. The nontrivial odd action
of the original supplement therefore excludes these literal component
quotients.

SporadicSieve applies these exclusions to the full A.3.6 alternatives on the
same component, retaining covering and nonquasisimple rows and common data.
Source: Aschbacher–Smith 3.3.12, argument (**), printed p.589; GLS3,
Tables 5.3a, 5.3b and 5.3e. The remaining recognition and terminal assembly
are owned by qt-d-1222-natural-line-action.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem stabilizer_two_of_restriction {H : Type*} [Group H]
    (P : Sylow 2 H) (hP : IsPGroup 2 (MulAut P))
    (hfix : ∀ a : MulAut H, (∀ x ∈ (P : Subgroup H), a x = x) →
      ∃ n : ℕ, a ^ (2 ^ n) = 1) :
    IsPGroup 2 (MulAction.stabilizer (MulAut H) (P : Subgroup H)) := by
  let B := MulAction.stabilizer (MulAut H) (P : Subgroup H)
  let r : B →* MulAut P := {
    toFun := fun a => (a.val.subgroupMap (P : Subgroup H)).trans
      (MulEquiv.subgroupCongr a.property)
    map_one' := by ext x; rfl
    map_mul' := by intro a b; ext x; rfl }
  intro a
  obtain ⟨n,hn⟩ := hP (r a)
  have he : r (a ^ (2 ^ n)) = 1 := (map_pow r a _).trans hn
  obtain ⟨m,hm⟩ := hfix (a.val ^ (2 ^ n)) (fun x hx =>
    congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : H)) he)
  refine ⟨n+m,Subtype.ext ?_⟩
  change a.val ^ (2 ^ (n+m)) = 1
  rw [pow_add,pow_mul]
  exact hm

private theorem all_stabilizers_two_of_one {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H)
    (hP : IsPGroup 2 (MulAction.stabilizer (MulAut H) (P : Subgroup H)))
    (Q : Sylow 2 H) :
    IsPGroup 2 (MulAction.stabilizer (MulAut H) (Q : Subgroup H)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P Q
  have he : (Q : Subgroup H) = MulAut.conj g • (P : Subgroup H) :=
    (congrArg Sylow.toSubgroup hg).symm
  exact hP.of_equiv (MulAction.stabilizerEquivStabilizer he)

private theorem mathieu_eleven_stabilizers (Q : Sylow 2 Sporadic.Mathieu.M11) :
    IsPGroup 2 (MulAction.stabilizer (MulAut Sporadic.Mathieu.M11)
      (Q : Subgroup Sporadic.Mathieu.M11)) := by
  open Sporadic.Mathieu in
    obtain ⟨P,a,b,ha,hb,hc,hgen⟩ := m11_exists_semidihedral_sylow
    have hcard : Nat.card P = 2^4 := by
      rw [P.card_eq_multiplicity,m11_order]
      decide +kernel
    have haut := Semidihedral.isPGroup_mulAut (n := 4) (by decide) hcard a b ha hb hc hgen
    apply all_stabilizers_two_of_one P (stabilizer_two_of_restriction P haut ?_) Q
    intro r hr
    obtain ⟨z,hz,rfl⟩ := m11_sylow_fixed_inner P r hr
    obtain ⟨n,hn⟩ := P.isPGroup' ⟨z,hz⟩
    refine ⟨n,?_⟩
    have hzpow : z ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [←map_pow,hzpow,map_one]

private theorem mathieu_twelve_stabilizers (Q : Sylow 2 Sporadic.Mathieu.M12) :
    IsPGroup 2 (MulAction.stabilizer (MulAut Sporadic.Mathieu.M12)
      (Q : Subgroup Sporadic.Mathieu.M12)) := by
  open Sporadic.Mathieu.M12SmallPair in
    apply all_stabilizers_two_of_one commonSylow
      (stabilizer_two_of_restriction commonSylow SylowAutomorphismGroup.isPGroup_two ?_) Q
    intro r hr
    rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow r hr with rfl | rfl
    · exact ⟨0,one_pow _⟩
    · refine ⟨1,?_⟩
      rw [pow_one,←map_pow,show z^2=1 by simpa only [z_order] using pow_orderOf_eq_one z,map_one]

private theorem mathieu_twentyfour_stabilizers (Q : Sylow 2 Sporadic.Mathieu.M24) :
    IsPGroup 2 (MulAction.stabilizer (MulAut Sporadic.Mathieu.M24)
      (Q : Subgroup Sporadic.Mathieu.M24)) := by
  open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer in
    apply MulAut.isPGroup_sylow_stabilizer_of_self_normalizing Q
    · exact le_antisymm
        (sylow_normalizer_le candidate_card (candidate_automorphisms_isPGroup candidate_card) Q)
        (Q : Subgroup M24).le_normalizer
    · exact M24OuterRestriction.outer_isPGroup_two

private theorem stabilizer_two_of_equiv {H M : Type*} [Group H] [Group M] [Finite H]
    (e : H ≃* M)
    (hM : ∀ P : Sylow 2 M,
      IsPGroup 2 (MulAction.stabilizer (MulAut M) (P : Subgroup M)))
    (P : Sylow 2 H) :
    IsPGroup 2 (MulAction.stabilizer (MulAut H) (P : Subgroup H)) := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := MulAction.stabilizer (MulAut H) (P : Subgroup H)
  let C := MulAction.stabilizer (MulAut M) (R : Subgroup M)
  have hp (a : B) : MulAut.congr e a.val ∈ C := by
    change ((P : Subgroup H).map e.toMonoidHom).map
      (MulAut.congr e a.val).toMonoidHom = (P : Subgroup H).map e.toMonoidHom
    have he : (MulAut.congr e a.val).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.val.toMonoidHom := by
      ext x
      exact congrArg e (congrArg a.val (e.symm_apply_apply x))
    rw [map_map,he,←map_map]
    have ha : (P : Subgroup H).map a.val.toMonoidHom = (P : Subgroup H) := a.property
    rw [ha]
  let j : B →* C := ((MulAut.congr e).toMonoidHom.comp B.subtype).codRestrict C hp
  exact (hM R).of_injective j (fun a b hab =>
    Subtype.ext ((MulAut.congr e).injective (congrArg Subtype.val hab)))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The Sylow stabilizer obstruction transports through an actual model isomorphism. -/
theorem quotient_not_equiv_two_stabilizers {M : Type*} [Group M]
    (hM : ∀ P : Sylow 2 M,
      IsPGroup 2 (MulAction.stabilizer (MulAut M) (P : Subgroup M))) :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* M) := by
  rintro ⟨e⟩
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  apply E.quotientSylow_stabilizer_not_twoGroup
  rw [←hP]
  exact stabilizer_two_of_equiv e hM P

/-- The M₁₁ row cannot support the actual odd supplement action. -/
theorem quotient_not_mathieu_eleven :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.Mathieu.M11) :=
  E.quotient_not_equiv_two_stabilizers mathieu_eleven_stabilizers

/-- The M₁₂ row cannot support the actual odd supplement action. -/
theorem quotient_not_mathieu_twelve :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.Mathieu.M12) :=
  E.quotient_not_equiv_two_stabilizers mathieu_twelve_stabilizers

/-- The M₂₄ row cannot support the actual odd supplement action. -/
theorem quotient_not_mathieu_twentyfour :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.Mathieu.M24) :=
  E.quotient_not_equiv_two_stabilizers mathieu_twentyfour_stabilizers

end MovedComponent
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
