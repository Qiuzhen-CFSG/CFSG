module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Requirements

/-!
# The actual two-dual quotient of a generated pair of full spans

Pass to the quotient of the starred group by Z_alpha. The radius-derived
bound makes this quotient abelian. Multiplication of the span images and
their marked coordinate maps then give the direct-sum quotient, with exact
kernel and the literal ambient conjugation equation on both coordinates.
The private product calculation follows the existing core-factor assembly
in Quotient/Factors.lean, with its kernel specialized here to Z_alpha.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12), printed p.912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
open Linear
namespace FullSpans

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

end FullSpans

variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- A genuine two-dual quotient of the actual starred group by Z_alpha. -/
structure StarDoubleQuotient where
  quotient : VStar R geometry (alpha R) (beta R) →* Multiplicative (W × W)
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Z R (alpha R)).subgroupOf (VStar R geometry (alpha R) (beta R))
  action : ∀ (m : M) (x y : VStar R geometry (alpha R) (beta R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd =
      (dual (common.natural.marking (source.projection m)) (quotient x).toAdd.1,
       dual (common.natural.marking (source.projection m)) (quotient x).toAdd.2)

variable {source common}

/-- Assemble the full-span maps without restricting their kernels to U_alpha. -/
theorem starDoubleQuotient_of_spans [Finite M] (radius : RadiusFacts R geometry)
    (c rho : Vertex R) (hc : (cosetGraph R).dist (alpha R) c = 2)
    (hrho : (cosetGraph R).dist (alpha R) rho = 2)
    (q : RankOne.SpanQuotient source common c) (r : RankOne.SpanQuotient source common rho)
    (hgen : VStar R geometry (alpha R) (beta R) = orbitSpan c ⊔ orbitSpan rho)
    (hinf : orbitSpan c ⊓ orbitSpan rho = Z R (alpha R)) :
    Nonempty (StarDoubleQuotient source common) := by
  let S := VStar R geometry (alpha R) (beta R)
  let A := (orbitSpan c).subgroupOf S
  let B := (orbitSpan rho).subgroupOf S
  let K := (Z R (alpha R)).subgroupOf S
  have hAS : orbitSpan c ≤ S := by
    change orbitSpan c ≤ VStar R geometry (alpha R) (beta R)
    rw [hgen]
    exact le_sup_left
  have hBS : orbitSpan rho ≤ S := by
    change orbitSpan rho ≤ VStar R geometry (alpha R) (beta R)
    rw [hgen]
    exact le_sup_right
  have hZA := RankOne.Z_le_orbitSpan_of_distance_two c hc
  have hZB := RankOne.Z_le_orbitSpan_of_distance_two rho hrho
  have hKA : K ≤ A := fun _ hx => hZA hx
  have hKB : K ≤ B := fun _ hx => hZB hx
  have hderived : _root_.commutator S ≤ K := by
    change _ ≤ (Z R (alpha R)).comap S.subtype
    rw [← map_le_iff_le_comap, map_subtype_commutator]
    exact ((commutator_mono (Flags.star_le_radius geometry _ _)
      (Flags.star_le_radius geometry _ _)).trans_eq
        (radius.radius_derived (alpha R) rfl)).trans (DistanceEight.U_le_Z R _)
  let eA : A ≃* orbitSpan c := subgroupOfEquivOfLe hAS
  let eB : B ≃* orbitSpan rho := subgroupOfEquivOfLe hBS
  let qA := q.quotient.comp eA.toMonoidHom
  let qB := r.quotient.comp eB.toMonoidHom
  have hkA : qA.ker = K.subgroupOf A := by
    ext x
    change eA x ∈ q.quotient.ker ↔ _
    rw [q.kernel]
    rfl
  have hkB : qB.ker = K.subgroupOf B := by
    ext x
    change eB x ∈ r.quotient.ker ↔ _
    rw [r.kernel]
    rfl
  have hsup : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup hAS hBS, ← hgen, subgroupOf_self]
  have hinter : A ⊓ B = K := by
    change (orbitSpan c ⊓ orbitSpan rho).subgroupOf S = K
    rw [hinf]
  obtain ⟨f, hfonto, hfker, hf⟩ := FullSpans.product_coordinates A B K hderived hKA hKB
    hsup hinter qA qB (q.onto.comp eA.surjective) (r.onto.comp eB.surjective) hkA hkB
  have hf' (a : orbitSpan c) (b : orbitSpan rho) :
      (f ⟨(a : FreeAmalgam R) * b, S.mul_mem (hAS a.property) (hBS b.property)⟩).toAdd =
        ((q.quotient a).toAdd, (r.quotient b).toAdd) :=
    hf ⟨⟨a, hAS a.property⟩, a.property⟩ ⟨⟨b, hBS b.property⟩, b.property⟩
  refine ⟨{ quotient := f, onto := hfonto, kernel := hfker, action := ?_ }⟩
  intro m x y hy
  let : B.Normal := Normal.of_commutator_le _ (hderived.trans hKB)
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
    (show x ∈ A ⊔ B by rw [hsup]; trivial)
  let a0 : orbitSpan c := ⟨a, ha⟩
  let b0 : orbitSpan rho := ⟨b, hb⟩
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let a' : orbitSpan c := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (orbitSpan_normalized c hm) _).mp ha⟩
  let b' : orbitSpan rho := ⟨embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (orbitSpan_normalized rho hm) _).mp hb⟩
  have hx : x = ⟨(a0 : FreeAmalgam R) * b0, S.mul_mem (hAS a0.property) (hBS b0.property)⟩ :=
    hab.symm
  have hy' : y = ⟨(a' : FreeAmalgam R) * b', S.mul_mem (hAS a'.property) (hBS b'.property)⟩ := by
    apply Subtype.ext
    rw [hy, ← hab]
    change embedM R m * ((a : FreeAmalgam R) * b) * (embedM R m)⁻¹ =
      (embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹) *
        (embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹)
    group
  rw [hy', hf', q.action m a0 a' rfl, r.action m b0 b' rfl, hx, hf']

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
