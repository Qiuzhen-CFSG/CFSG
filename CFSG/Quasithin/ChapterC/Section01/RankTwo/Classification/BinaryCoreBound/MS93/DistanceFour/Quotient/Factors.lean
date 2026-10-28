module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Single
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Assembling two actual dual factors of the core

Two normalized subgroups containing U_alpha, meeting precisely in U_alpha
and generating the actual core, suffice to construct the displayed double
quotient. The factor maps must be surjective, have their exact relative
kernels, and intertwine the given conjugation and natural marking.

The proof passes to the quotient by U_alpha. Radius-derived containment
makes this quotient abelian. Multiplication of the two factors followed by
that quotient is a surjective homomorphism; their two coordinate maps kill
its kernel and therefore descend. The resulting map has kernel exactly
U_alpha, and its action equation follows on products of factor elements.

This is the final quotient assembly for MS93 (1993), (4.6.12), pp.910--912.
`DualFactor` is a conditional interface; neither its constructors nor the
two geometric subgroups are assumed to exist without further proof.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Linear

private theorem product_coordinates {G : Type*} [Group G]
    (A B K : Subgroup G) (hderived : _root_.commutator G ≤ K)
    (hA : K ≤ A) (hB : K ≤ B) (hgen : A ⊔ B = ⊤) (hinf : A ⊓ B = K)
    (qA : A →* Multiplicative W) (qB : B →* Multiplicative W)
    (hontoA : Function.Surjective qA) (hontoB : Function.Surjective qB)
    (hkerA : qA.ker = K.subgroupOf A) (hkerB : qB.ker = K.subgroupOf B) :
    ∃ q : G →* Multiplicative (W × W), Function.Surjective q ∧ q.ker = K ∧
      ∀ (a : A) (b : B), (q ((a : G) * b)).toAdd = ((qA a).toAdd, (qB b).toAdd) := by
  let : K.Normal := Normal.of_commutator_le G hderived
  let : B.Normal := Normal.of_commutator_le G (hderived.trans hB)
  let : IsMulCommutative (G ⧸ K) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let π := QuotientGroup.mk' K
  have hdecomp (x : G) : ∃ (a : A) (b : B), (a : G) * b = x := by
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
      (show x ∈ A ⊔ B by rw [hgen]; trivial)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  let f : A × B →* G ⧸ K :=
    (π.comp A.subtype).noncommCoprod (π.comp B.subtype) (fun _ _ => mul_comm' _ _)
  have hf (a : A) (b : B) : f (a, b) = π ((a : G) * b) := (π.map_mul _ _).symm
  have honto : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K z
    obtain ⟨a, b, rfl⟩ := hdecomp x
    exact ⟨(a, b), hf a b⟩
  let g : A × B →* Multiplicative (W × W) := {
    toFun x := Multiplicative.ofAdd ((qA x.1).toAdd, (qB x.2).toAdd)
    map_one' := by simp
    map_mul' := by intros; simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; rfl }
  have hgker : f.ker ≤ g.ker := by
    rintro ⟨a, b⟩ hab
    have habK : (a : G) * b ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact (hf a b).symm.trans hab
    have hbA : (b : G) ∈ A := by
      have h := A.mul_mem (A.inv_mem a.property) (hA habK)
      simpa only [inv_mul_cancel_left] using h
    have hbK : (b : G) ∈ K := hinf ▸ (show (b : G) ∈ A ⊓ B from ⟨hbA, b.property⟩)
    have haK : (a : G) ∈ K := by
      have h := K.mul_mem habK (K.inv_mem hbK)
      simpa only [mul_inv_cancel_right] using h
    have ha1 : qA a = 1 := by change a ∈ qA.ker; rw [hkerA]; exact haK
    have hb1 : qB b = 1 := by change b ∈ qB.ker; rw [hkerB]; exact hbK
    change Multiplicative.ofAdd ((qA a).toAdd, (qB b).toAdd) = 1
    rw [ha1, hb1]
    rfl
  let lift : (G ⧸ K) →* Multiplicative (W × W) := f.liftOfSurjective honto ⟨g, hgker⟩
  let q := lift.comp π
  have hq (a : A) (b : B) : q ((a : G) * b) = g (a, b) := by
    change lift (π ((a : G) * b)) = _
    rw [← hf]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨q, ?_, ?_, fun a b => congrArg Multiplicative.toAdd (hq a b)⟩
  · intro z
    obtain ⟨a, ha⟩ := hontoA (Multiplicative.ofAdd z.toAdd.1)
    obtain ⟨b, hb⟩ := hontoB (Multiplicative.ofAdd z.toAdd.2)
    refine ⟨(a : G) * b, (hq a b).trans ?_⟩
    change Multiplicative.ofAdd ((qA a).toAdd, (qB b).toAdd) = z
    rw [ha, hb]
    rfl
  · ext x
    obtain ⟨a, b, rfl⟩ := hdecomp x
    change q ((a : G) * b) = 1 ↔ _
    rw [hq]
    constructor
    · intro h
      have ha : qA a = 1 := congrArg (fun z : Multiplicative (W × W) =>
        Multiplicative.ofAdd z.toAdd.1) h
      have hb : qB b = 1 := congrArg (fun z : Multiplicative (W × W) =>
        Multiplicative.ofAdd z.toAdd.2) h
      have haK : (a : G) ∈ K := by change a ∈ K.subgroupOf A; rw [← hkerA]; exact ha
      have hbK : (b : G) ∈ K := by change b ∈ K.subgroupOf B; rw [← hkerB]; exact hb
      exact K.mul_mem haK hbK
    · intro hx
      have hf0 : f (a, b) = 1 := (hf a b).trans ((QuotientGroup.eq_one_iff _).mpr hx)
      exact hgker hf0

variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R} (common : CommonFacts R source geometry)

structure DualFactor (F : Subgroup (core R (alpha R))) where
  contains : (U R (alpha R)).subgroupOf (core R (alpha R)) ≤ F
  normalized : ∀ m (x : core R (alpha R)), x ∈ F → coreAction (R := R) m x ∈ F
  quotient : F →* Multiplicative W
  onto : Function.Surjective quotient
  kernel : quotient.ker =
    ((U R (alpha R)).subgroupOf (core R (alpha R))).subgroupOf F
  action : ∀ (m : M) (x y : F),
    (y : core R (alpha R)) = coreAction (R := R) m x →
    (quotient y).toAdd = dual (common.natural.marking (source.projection m)) (quotient x).toAdd

theorem doubleDualQuotient_of_factors [Finite M] (radius : RadiusFacts R geometry)
    (A B : Subgroup (core R (alpha R)))
    (dA : DualFactor source common A) (dB : DualFactor source common B)
    (hgen : A ⊔ B = ⊤)
    (hinf : A ⊓ B = (U R (alpha R)).subgroupOf (core R (alpha R))) :
    Nonempty (DoubleDualQuotient source common) := by
  have hderived : _root_.commutator (core R (alpha R)) ≤
      (U R (alpha R)).subgroupOf (core R (alpha R)) := by
    change _ ≤ (U R (alpha R)).comap (core R (alpha R)).subtype
    rw [← map_le_iff_le_comap, map_subtype_commutator]
    rw [← radius.radius_derived (alpha R) rfl]
    exact commutator_mono (radius.core_le_radius (alpha R) rfl)
      (radius.core_le_radius (alpha R) rfl)
  obtain ⟨q, honto, hker, hq⟩ := product_coordinates A B _ hderived dA.contains dB.contains
    hgen hinf dA.quotient dB.quotient dA.onto dB.onto dA.kernel dB.kernel
  refine ⟨{
    quotient := q
    onto := honto
    kernel := hker
    noncommutative := core_not_commutative source geometry common radius
    action := ?_ }⟩
  intro m x y hy
  have hxy : y = coreAction (R := R) m x := Subtype.ext hy
  let : B.Normal := Normal.of_commutator_le _ (hderived.trans dB.contains)
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
    (show x ∈ A ⊔ B by rw [hgen]; trivial)
  let a' : A := ⟨coreAction (R := R) m a, dA.normalized m a ha⟩
  let b' : B := ⟨coreAction (R := R) m b, dB.normalized m b hb⟩
  have hya : y = (a' : core R (alpha R)) * b' := by
    rw [hxy, ← hab, map_mul]
  rw [hya, hq, dA.action m ⟨a, ha⟩ a' rfl, dB.action m ⟨b, hb⟩ b' rfl, ← hab,
    hq ⟨a, ha⟩ ⟨b, hb⟩]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
