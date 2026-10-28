module
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.SubgroupGeometryAssembly
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Transporting the exceptional normal-closure alternatives

Pull a relatively normal subgroup back through the one marked exceptional
Sylow isomorphism. Squares in the same marked central involution subgroup
make its central quotient elementary abelian. The native subgroup geometry
then gives either center Z inside S or equality with the quaternion core Q.
All groups and the central involution use the same embedding.

Source: Aschbacher--Smith §5.3.7, printed pp.660--661 (`refs/quasithin.pdf`).
The Chapter6 source consumer constructs the normal closure and discharges
its normality, square and Sylow-containment premises.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G]

private theorem centerIn_map_injective {K : Type*} [Group K]
    (P : Subgroup K) (f : K →* G) (hf : Function.Injective f) :
    centerIn (P.map f) = (centerIn P).map f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := hx.1
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    intro b hb
    apply hf
    simpa only [map_mul] using hx.2 (f b) (mem_map_of_mem f hb)
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem f ha.1,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    simpa only [map_mul] using congrArg f (ha.2 b hb)

/-- The marked nonabelian alternatives use the same ambient embedding for
the unipotent group, its central line, and the quaternion core. -/
theorem marked_normalClosure_alternatives
    (c : Section03ExceptionalSylowModel.MarkedCopy G) (P : Subgroup G)
    (hP : P ≤ c.carrier) (hn : c.carrier ≤ normalizer (P : Set G))
    (hZ : c.Z ≤ P) (hsq : ∀ a ∈ P, a^2 ∈ zpowers c.z)
    (hna : ¬ IsMulCommutative P) :
    (P ≤ c.S ∧ centerIn P = c.Z) ∨ P = c.Q := by
  let R := P.comap c.embedding
  have hmap : R.map c.embedding = P := by
    apply map_comap_eq_self
    intro x hx
    obtain ⟨a,ha⟩ := c.equiv.surjective ⟨x,hP hx⟩
    exact ⟨a,congrArg Subtype.val ha⟩
  have hRnormal : R.Normal := ⟨fun a ha g => by
    change c.embedding (g*a*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp hn _ (c.equiv g).property _ ha⟩
  have hZR : Matrix.PSL3Four.SylowModel.Z ≤ R := fun a ha => hZ (mem_map_of_mem _ ha)
  have hRsq (a : Matrix.PSL3Four.SylowModel.T) (ha : a ∈ R) :
      a^2 ∈ Matrix.PSL3Four.SylowModel.C := by
    have hh := hsq (c.embedding a) ha
    have hmapC : Matrix.PSL3Four.SylowModel.C.map c.embedding = zpowers c.z :=
      c.embedding.map_zpowers _
    rw [←hmapC,←map_pow] at hh
    obtain ⟨b,hb,hb'⟩ := hh
    exact c.embedding_injective hb' ▸ hb
  have hbar : IsElementaryAbelian 2 (R.map Matrix.PSL3Four.SylowModel.quotient) := by
    have hs (a : R.map Matrix.PSL3Four.SylowModel.quotient) : a^2=1 := by
      apply Subtype.ext
      obtain ⟨b,hb,he⟩ := a.property
      change a.val^2=1
      rw [←he,←map_pow]
      exact (QuotientGroup.eq_one_iff (N := Matrix.PSL3Four.SylowModel.C) (b^2)).mpr (hRsq b hb)
    refine { toIsMulCommutative := ?_, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    have hi (a : R.map Matrix.PSL3Four.SylowModel.quotient) : a⁻¹=a :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs a)
    exact ⟨⟨fun a b => by rw [←hi (a*b),mul_inv_rev,hi a,hi b]⟩⟩
  have hRna : ¬ IsMulCommutative R := by
    intro hc
    let := hc
    have hh : IsMulCommutative (R.map c.embedding) := Subgroup.map_isMulCommutative R c.embedding
    exact hna (hmap ▸ hh)
  rcases Matrix.PSL3Four.SylowModel.normal_nonabelian_alternatives R hRnormal hZR hbar hRna
    with ⟨hle,hcenter⟩ | heq
  · left
    refine ⟨?_,?_⟩
    · rw [←hmap]
      exact map_mono hle
    · rw [←hmap,centerIn_map_injective R c.embedding c.embedding_injective,
        centerIn_eq_map_center,hcenter]
      rfl
  · right
    rw [←hmap,heq]
    rfl
end CFSG.Quasithin.Chapter5.Section03LinearSource
