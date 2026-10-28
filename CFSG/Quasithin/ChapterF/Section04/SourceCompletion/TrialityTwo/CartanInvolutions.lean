module
public import Theory.SpecificGroups.Triality.BinaryTorusInvolutions
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanCoordinates

/-!
# Four binary coordinates for the marked triality reflection pair

At the central endpoint involutivity eliminates the order-seven torus factor.
Conjugating both endpoints by the fourth power of the arms torus parameter
removes the other factor. The right word is fixed by that same conjugation.
The two commuting squares identify the ambient conjugations, so the actual
sixth-power equation, product order and escape from the whole Borel survive.

The native involution equations then leave two binary scalars at each endpoint.
Every resulting word normalizes the same marked torus. Applying the existing
order-bound construction therefore gives sixteen explicit candidate pairs
without changing either endpoint map. The matching native sixth-power equation
and recognition remain unproved here.
Source: Aschbacher--Smith F.4.15--17, pp.281--283 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.BinaryTorusEndpoints
variable {G : Type*} [Group G] (c : Completion G)

/-- The same two endpoint maps, after one common torus conjugation, have
only four binary parameters. No native product relation is assumed. -/
theorem reduce_involution_coordinates
    (a : Fin 3 → fixedField parameters) (b : fixedField parameters)
    (d : Fin 3 → fixedField parameters) (z w : torus parameters)
    (hs : (endpointWord .arms a 0 z)^2=1)
    (ht : (endpointWord .central (Pi.single 0 b) d w)^2=1)
    (hsout : c.left (endpointWord .arms a 0 z)∉c.middle.range)
    (htout : c.right (endpointWord .central (Pi.single 0 b) d w)∉c.middle.range)
    (hpow : (c.left (endpointWord .arms a 0 z)*
      c.right (endpointWord .central (Pi.single 0 b) d w))^6=1)
    (ho : orderOf (c.left (endpointWord .arms a 0 z)*
      c.right (endpointWord .central (Pi.single 0 b) d w))=6) :
    ∃ p q b j : fixedField parameters,
      let s := endpointWord .arms ![p,p,q] 0 1
      let t := endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  have hw := central_involution_torus_eq_one (Pi.single 0 b) d w ht
  subst w
  let u := torusBorel (z^4)
  let A := MulAut.conj (c.middle u)
  let sa := MulAut.conj (amalgam.left u)
  let ta := MulAut.conj (amalgam.right u)
  let s := endpointWord .arms a 0 z
  let t := endpointWord .central (Pi.single 0 b) d 1
  let s' := endpointWord .arms a 0 1
  have he : sa s=s' := arms_torus_conjugation a z
  have hf : ta t=t := central_torus_conjugation (Pi.single 0 b) d (z^4)
  have hs' : s'^2=1 := by
    rw [←he,←map_pow]
    change sa (s^2)=1
    rw [hs,map_one]
  have hmL (x : parabolic parameters .arms) : c.left (sa x)=A (c.left x) := by
    simp only [sa,A,MulAut.conj_apply,map_mul,map_inv]
    rfl
  have hmR (x : parabolic parameters .central) : c.right (ta x)=A (c.right x) := by
    have hu : c.right (amalgam.right u)=c.middle u :=
      (DFunLike.congr_fun c.compatible u).symm
    simp only [ta,A,MulAut.conj_apply,map_mul,map_inv,hu]
  have hse : c.left s'=A (c.left s) := by rw [←he,hmL]
  have hte : c.right t=A (c.right t) := by rw [←hmR,hf]
  have hso : c.left s'∉c.middle.range := by
    rw [hse]
    intro hh
    exact hsout ((mem_normalizer_iff.mp
      (c.middle.range.le_normalizer ⟨u,rfl⟩) (c.left s)).mpr hh)
  have hto : c.right t∉c.middle.range := htout
  have hp : (c.left s'*c.right t)^6=1 := by
    calc
      _ = (A (c.left s)*A (c.right t))^6 := congrArg₂ (fun x y => (x*y)^6) hse hte
      _ = A ((c.left s*c.right t)^6) := by rw [←map_mul,←map_pow]
      _ = 1 := by rw [hpow,map_one]
  have horder : orderOf (c.left s'*c.right t)=6 := by
    calc
      _ = orderOf (A (c.left s)*A (c.right t)) := congrArg₂ (fun x y => orderOf (x*y)) hse hte
      _ = orderOf (c.left s*c.right t) := by rw [←map_mul,A.orderOf_eq]
      _ = 6 := ho
  obtain ⟨hsa,hta⟩ := involution_coordinate_words a b d hs' ht
  refine ⟨a 0,a 2,b,d 1,?_⟩
  dsimp only
  rw [←hsa,←hta]
  exact ⟨hs',ht,hso,hto,hp,horder⟩

private theorem torus_model_map : borelTorus.map modelCompletion.middle = torus parameters := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x,torus_le_borel parameters hx⟩,hx,rfl⟩

/-- The left coordinate word retains the literal marked torus normalizer. -/
theorem left_coordinate_normalizes (a b : Fin 3 → fixedField parameters) (z : torus parameters) :
    c.left (endpointWord .arms a b z)∈normalizer (borelTorus.map c.middle:Set G) := by
  apply (c.left_normalizes_middle_iff modelCompletion borelTorus _).mpr
  rw [torus_model_map]
  exact endpointWord_normalizes .arms a b z

/-- The right coordinate word retains the same torus through its commuting square. -/
theorem right_coordinate_normalizes (a b : Fin 3 → fixedField parameters) (z : torus parameters) :
    c.right (endpointWord .central a b z)∈normalizer (borelTorus.map c.middle:Set G) := by
  apply (c.right_normalizes_middle_iff modelCompletion borelTorus _).mpr
  rw [torus_model_map]
  exact endpointWord_normalizes .central a b z

variable [Finite G]

/-- An order-bounded completion supplies a matching candidate among just
sixteen native pairs, retaining the given full endpoint markings. -/
theorem exists_four_coordinate_involutions_of_order_bound
    (horder : Nat.card G≤Nat.card Model) :
    ∃ p q b j : fixedField parameters,
      let s := endpointWord .arms ![p,p,q] 0 1
      let t := endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  obtain ⟨a,b,d,z,w,hs,ht,hsout,htout,hpow,ho,_⟩ :=
    c.exists_endpoint_coordinates_of_order_bound horder
  exact c.reduce_involution_coordinates a b d z w hs ht hsout htout hpow ho

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
