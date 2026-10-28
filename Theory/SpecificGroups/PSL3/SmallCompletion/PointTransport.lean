module
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon

/-!
# Point coordinates from short paths in a coset plane

Every point is the root or the endpoint of its unique nonbacktracking two-edge
path from the root. A common coset cover therefore identifies the point sets
of two diameter-three geometries, equivariantly for the literal root stabilizer.
This is the local action comparison in Aschbacher–Smith F.3.3–4 and F.4.8,
printed pp.270,278 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
namespace Subgroup.CosetGeometry.RankTwo.PointCoordinates
variable {A : Type*} [Group A] (P : Bool → Subgroup A)
attribute [local instance] Subgroup.CosetGeometry.RankTwo.pathAction
attribute [local instance] Subgroup.CosetGeometry.RankTwo.nonbacktrackingAction
abbrev TwoPaths (v : Vertex P) := {p : BasedWalk (graph P) 2 v // p.Nonbacktracking}

def endpoint (v : Vertex P) (p : Option (TwoPaths P v)) : Fiber P v.type :=
  match p with
  | none => ⟨v,rfl⟩
  | some p => ⟨p.val.endpoint, by
      have h₁ := p.val.1.property.1
      have h₂ := p.val.2.1.property.1
      change p.val.2.1.val.type = v.type
      cases hv : v.type <;> cases h1 : p.val.1.val.type <;>
        cases h2 : p.val.2.1.val.type <;> simp_all⟩

variable (hgen : P false ⊔ P true = ⊤)
    (hu : (graph P).UniqueGeodesicsBelow 3)
    (hd : ∀ v w, (graph P).dist v w ≤ 3)

include hgen hu hd in
theorem endpoint_bijective (v : Vertex P) : Function.Bijective (endpoint P v) := by
  constructor
  · intro p q he
    have he' := congrArg Subtype.val he
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q => exact (q.property.1 he'.symm).elim
    | some p =>
      cases q with
      | none => exact (p.property.1 he').elim
      | some q =>
        have heq : p.val.2.1.val = q.val.2.1.val := he'
        obtain ⟨w,hw,huniq⟩ := existsUnique_commonNeighbor_of_plane_geometry P hgen hu hd
          (endpoint P v (some p)).property.symm p.property.1.symm
        have hm : p.val.1.val = q.val.1.val :=
          (huniq p.val.1.val ⟨p.val.1.property,p.val.2.1.property.symm⟩).trans
            (huniq q.val.1.val ⟨q.val.1.property,heq.symm ▸ q.val.2.1.property.symm⟩).symm
        congr 1
        apply Subtype.ext
        apply BasedWalk.vertices_injective
        change [v,p.val.1.val,p.val.2.1.val] = [v,q.val.1.val,q.val.2.1.val]
        exact congrArg (List.cons v) (congrArg₂ List.cons hm (congrArg (fun z => [z]) heq))
  · intro w
    by_cases he : w.val = v
    · exact ⟨none,Subtype.ext he.symm⟩
    · obtain ⟨z,hz,_⟩ := existsUnique_commonNeighbor_of_plane_geometry P hgen hu hd
        w.property.symm (Ne.symm he)
      exact ⟨some ⟨⟨⟨z,hz.1⟩,⟨⟨w.val,hz.2.symm⟩,PUnit.unit⟩⟩,he,trivial⟩,rfl⟩

/-- Points of one type are exactly the root and the endpoints of two-edge paths. -/
def endpointEquiv (v : Vertex P) : Option (TwoPaths P v) ≃ Fiber P v.type :=
  Equiv.ofBijective (endpoint P v) (endpoint_bijective P hgen hu hd v)

local instance (v : Vertex P) : MulAction (stabilizer P v) (BasedWalk (graph P) 2 v) :=
  Subgroup.CosetGeometry.RankTwo.pathAction P 2 v
local instance (v : Vertex P) : MulAction (stabilizer P v) (TwoPaths P v) :=
  Subgroup.CosetGeometry.RankTwo.nonbacktrackingAction P 2 v

theorem endpoint_smul (v : Vertex P) (a : stabilizer P v) (p : TwoPaths P v) :
    endpoint P v (some (a • p)) = a.val • endpoint P v (some p) := by
  apply Subtype.ext
  change (a • p.val).endpoint = a.val • p.val.endpoint
  apply Eq.symm
  apply endpoint_smul_of_vertices (show GraphAction (graph P) A from
    ⟨fun g => (translationGraphIso P g).toHom.map_adj⟩)
  exact (vertices_smul_path P a p.val).symm

variable {B C : Type*} [Group B] [Group C]
variable {P} {Q : Bool → Subgroup B} {R : Bool → Subgroup C}
variable {f : A →* B} {g : A →* C}
variable (c : CoverData P Q f) (d : CoverData P R g)
variable (hq : Q false ⊔ Q true=⊤) (hr : R false ⊔ R true=⊤)
variable (uq : (graph Q).UniqueGeodesicsBelow 3) (ur : (graph R).UniqueGeodesicsBelow 3)
variable (dq : ∀v w,(graph Q).dist v w≤3) (dr : ∀v w,(graph R).dist v w≤3)

/-- A common coset cover identifies the entire same-type fiber by short paths. -/
def compare (v : Vertex P) : Fiber Q (c.vertex v).type ≃ Fiber R (d.vertex v).type :=
  (endpointEquiv Q hq uq dq (c.vertex v)).symm.trans
    ((Equiv.optionCongr (c.transportNbPathEquiv d 2 v)).trans
      (endpointEquiv R hr ur dr (d.vertex v)))

theorem compare_base (v : Vertex P) :
    compare c d hq hr uq ur dq dr v ⟨c.vertex v,rfl⟩ = ⟨d.vertex v,rfl⟩ := by
  change compare c d hq hr uq ur dq dr v
    (endpointEquiv Q hq uq dq (c.vertex v) none) = _
  unfold compare
  rw [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem compare_path (v : Vertex P) (p : TwoPaths P v) :
    compare c d hq hr uq ur dq dr v
      (endpoint Q (c.vertex v) (some (c.nbPathEquiv 2 v p))) =
      endpoint R (d.vertex v) (some (d.nbPathEquiv 2 v p)) := by
  change compare c d hq hr uq ur dq dr v
    (endpointEquiv Q hq uq dq (c.vertex v) (some (c.nbPathEquiv 2 v p))) = _
  unfold compare
  rw [Equiv.trans_apply,Equiv.symm_apply_apply]
  change endpoint R (d.vertex v) (some (d.nbPathEquiv 2 v ((c.nbPathEquiv 2 v).symm (c.nbPathEquiv 2 v p)))) = _
  rw [Equiv.symm_apply_apply]

/-- Exact equivariance under the whole marked root endpoint. -/
theorem compare_smul (v : Vertex P) (a : stabilizer P v) (x : Fiber Q v.type) :
    compare c d hq hr uq ur dq dr v (f a • x) =
      g a • compare c d hq hr uq ur dq dr v x := by
  obtain ⟨p,rfl⟩ := (endpointEquiv Q hq uq dq (c.vertex v)).surjective x
  cases p with
  | none =>
    have hf : f a • (⟨c.vertex v,rfl⟩ : Fiber Q v.type) = ⟨c.vertex v,rfl⟩ :=
      Subtype.ext (c.stabilizerEquiv v a).property
    change compare c d hq hr uq ur dq dr v (f a • ⟨c.vertex v,rfl⟩) =
      g a • compare c d hq hr uq ur dq dr v ⟨c.vertex v,rfl⟩
    rw [hf,compare_base]
    exact Subtype.ext (d.stabilizerEquiv v a).property.symm
  | some p =>
    obtain ⟨p,rfl⟩ := (c.nbPathEquiv 2 v).surjective p
    change compare c d hq hr uq ur dq dr v
      (f a • endpoint Q (c.vertex v) (some (c.nbPathEquiv 2 v p))) =
      g a • compare c d hq hr uq ur dq dr v
        (endpoint Q (c.vertex v) (some (c.nbPathEquiv 2 v p)))
    have hx := endpoint_smul Q (c.vertex v) (c.stabilizerEquiv v a) (c.nbPathEquiv 2 v p)
    change endpoint Q (c.vertex v) (some (c.stabilizerEquiv v a • c.nbPathEquiv 2 v p)) =
      f a • endpoint Q (c.vertex v) (some (c.nbPathEquiv 2 v p)) at hx
    rw [←hx,←c.nbPathEquiv_smul,compare_path,compare_path,d.nbPathEquiv_smul]
    exact endpoint_smul R (d.vertex v) (d.stabilizerEquiv v a) _
end Subgroup.CosetGeometry.RankTwo.PointCoordinates
