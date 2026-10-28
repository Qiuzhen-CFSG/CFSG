module
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximal nonsingular stabilizers in the binary four-space doubled action

The automorphism group of GL₄(2) acts primitively on the 120 nonsingular
vectors of its natural-plus-dual module. Four elementary matrices and the
graph automorphism give a small checked proof: a spanning forest for the
point stabilizer has five roots, and six explicit word calculations connect
all roots whenever an overgroup moves the base point. Transitivity then
forces that overgroup to be the whole automorphism group. The arrays below
are path certificates, whose edges and depths are checked by the kernel.
The dual action is verified symbolically using the dot product.

The public theorem applies to any coordinate action with the prescribed
inner and graph actions and any nonsingular vector. Its source consumer is
the maximal point join in the degree-four normal-residual branch of 12.1.1.

Source: Aschbacher--Smith, H.9.1(4) and 12.1.1, printed pp.390,788--789.
-/

open BinaryLinear BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.VectorStabilizers.FourMaximal
section

def bits (a : Fin 16) : Fin 4 → ZMod 2 := fun i => (a.val / 2^i.val : ℕ)
def coord (p : Fin 256) : CoordinateSpace 4 :=
  (bits ⟨p.val / 16, by omega⟩,
    dotProductEquiv (ZMod 2) (Fin 4) (bits ⟨p.val % 16, Nat.mod_lt _ (by decide)⟩))
def good (p : Fin 256) : Prop :=
  dotProduct (bits ⟨p.val % 16, Nat.mod_lt _ (by decide)⟩)
    (bits ⟨p.val / 16, by omega⟩) = 1
instance (p : Fin 256) : Decidable (good p) := inferInstanceAs (Decidable (_ = (1 : ZMod 2)))
def row : Fin 4 → Fin 4 := ![1,2,3,0]
def col : Fin 4 → Fin 4 := ![2,3,1,1]
def move (i : Fin 5) (p : Fin 256) : Fin 256 :=
  if hi : i.val = 4 then ⟨16*(p.val % 16)+p.val/16, by omega⟩ else
  let j : Fin 4 := ⟨i.val, by omega⟩
  let x := p.val / 16
  let y := p.val % 16
  ⟨(16*(Nat.xor x (((x / 2^(col j).val) % 2) * 2^(row j).val)) +
    Nat.xor y (((y / 2^(row j).val) % 2) * 2^(col j).val)) % 256,
    Nat.mod_lt _ (by decide)⟩

def root (p : Fin 256) : Fin 256 :=
  (#[17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,19,17,19,17,19,17,19,17,19,17,19,17,19,17,17,34,35,17,17,34,35,17,17,34,35,17,17,34,35,17,19,35,17,17,53,35,17,17,53,35,17,17,53,35,17,17,17,17,17,34,35,34,35,17,17,17,17,34,35,34,35,17,19,17,53,35,17,35,17,17,53,17,53,35,17,35,17,17,17,34,35,34,35,17,17,17,17,34,35,34,35,17,17,17,19,35,17,35,17,17,53,17,53,35,17,35,17,17,53,17,17,17,17,17,17,17,17,34,35,34,35,34,35,34,35,17,19,17,53,17,53,17,53,35,17,35,17,35,17,35,17,17,17,34,35,17,17,34,35,34,35,17,17,34,35,17,17,17,19,35,17,17,53,35,17,35,17,17,53,35,17,17,53,17,17,17,17,34,35,34,35,34,35,34,35,17,17,17,17,17,19,17,53,35,17,35,17,35,17,35,17,17,53,17,53,17,17,34,35,34,35,17,17,34,35,17,17,17,17,34,35,17,19,35,17,35,17,17,53,35,17,17,53,17,53,35,17] : Array (Fin 256))[p.val]!

def parent (p : Fin 256) : Fin 256 :=
  (#[17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,19,17,29,17,19,17,27,17,31,17,31,17,23,17,17,34,35,17,17,34,35,17,17,162,47,17,17,38,39,17,19,35,17,17,53,50,17,17,187,163,17,17,53,227,17,17,17,17,17,100,101,98,99,17,17,17,17,108,109,106,71,17,113,17,53,92,17,114,17,17,91,17,181,94,17,122,17,17,17,38,227,70,86,17,17,17,17,166,182,238,239,17,17,17,23,39,17,124,17,17,83,17,251,167,17,199,17,17,253,17,17,17,17,17,17,17,17,138,139,168,184,142,143,198,199,17,25,17,211,17,221,17,147,154,17,169,17,158,17,214,17,17,17,34,35,17,17,38,39,42,43,17,17,46,47,17,17,17,49,50,17,17,53,54,17,58,17,17,191,62,17,17,61,17,17,17,17,228,229,226,227,202,203,172,239,17,17,17,17,17,29,17,61,77,17,242,17,218,17,173,17,17,253,17,253,17,17,162,163,172,173,17,17,106,169,17,17,17,17,166,167,17,31,47,17,188,17,17,191,122,17,17,191,17,181,239,17] : Array (Fin 256))[p.val]!

def depth (p : Fin 256) : ℕ :=
  (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,1,0,4,0,3,0,3,0,2,0,0,0,0,0,0,1,1,0,0,2,3,0,0,2,2,0,1,1,0,0,0,2,0,0,4,2,0,0,1,3,0,0,0,0,0,5,5,3,4,0,0,0,0,5,5,4,5,0,3,0,1,6,0,3,0,0,3,0,2,5,0,4,0,0,0,2,3,4,4,0,0,0,0,3,4,4,4,0,0,0,2,2,0,5,0,0,2,0,4,3,0,4,0,0,3,0,0,0,0,0,0,0,0,5,5,4,4,5,5,4,4,0,5,0,3,0,4,0,4,6,0,5,0,6,0,5,0,0,0,1,1,0,0,2,2,3,4,0,0,3,3,0,0,0,2,2,0,0,1,3,0,3,0,0,3,4,0,0,2,0,0,0,0,5,5,3,3,5,5,4,4,0,0,0,0,0,4,0,2,6,0,4,0,5,0,4,0,0,3,0,3,0,0,2,2,4,4,0,0,4,5,0,0,0,0,3,3,0,3,3,0,5,0,0,3,4,0,0,3,0,2,4,0] : Array (ℕ))[p.val]!

def edge (p : Fin 256) : Fin 5 :=
  (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,1,0,4,4,0,0,0,0,0,0,2,4,0,0,1,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,4,1,0,0,0,0,2,0,4,2,0,0,0,0,0,4,2,4,4,0,0,0,0,4,4,2,2,0,0,0,4,4,0,1,0,0,0,0,2,4,0,4,0,0,2,0,0,0,0,0,0,0,0,2,2,4,4,2,2,1,1,0,4,0,1,0,1,0,0,2,0,4,0,2,0,1,0,0,0,2,2,0,0,2,2,2,2,0,0,2,2,0,0,0,2,2,0,0,2,2,0,2,0,0,0,2,0,0,2,0,0,0,0,0,0,0,0,2,2,4,0,0,0,0,0,0,4,0,4,4,0,0,0,2,0,4,0,0,0,0,4,0,0,1,1,1,1,0,0,2,1,0,0,0,0,1,1,0,4,4,0,1,0,0,1,2,0,0,4,0,1,4,0] : Array (Fin 5))[p.val]!

theorem forest (p : Fin 256) (hp : good p) : p = root p ∨
    (good (parent p) ∧ depth (parent p) < depth p ∧ root (parent p) = root p ∧
      edge p ≠ 3 ∧ move (edge p) (parent p) = p) := by
  revert p
  decide +kernel +revert

theorem roots (p : Fin 256) (hp : good p) :
    root p = 17 ∨ root p = 19 ∨ root p = 34 ∨ root p = 35 ∨ root p = 53 := by
  revert p
  decide +kernel +revert

theorem root_base (p : Fin 256) (hp : good p) : root p = 17 ↔ p = 17 := by
  revert p
  decide +kernel +revert


def linearGenerator (i : Fin 4) : LinearGroup 4 :=
  transvection (Pi.single (row i) 1) (LinearMap.proj (col i)) (by
    have h : col i ≠ row i := by revert i; decide
    simp [h])

noncomputable def generator (i : Fin 5) : MulAut (LinearGroup 4) :=
  if hi : i.val = 4 then graphLinear 4 else
    MulAut.conj (linearGenerator ⟨i.val, by omega⟩)

private theorem natural_move (i : Fin 4) (p : Fin 256) :
    bits ⟨p.val/16,by omega⟩ +
      (bits ⟨p.val/16,by omega⟩ (col i)) • Pi.single (row i) 1 =
        bits ⟨(move i.castSucc p).val / 16,by omega⟩ := by
  revert i p
  decide +kernel

private theorem dual_move (i : Fin 4) (p : Fin 256) :
    bits ⟨(move i.castSucc p).val % 16,Nat.mod_lt _ (by decide)⟩ =
      bits ⟨p.val%16,Nat.mod_lt _ (by decide)⟩ +
      (bits ⟨p.val%16,Nat.mod_lt _ (by decide)⟩ (row i)) • Pi.single (col i) 1 := by
  revert i p
  decide +kernel

theorem generator_coord (d : CoordinateAction 4) (i : Fin 5) (p : Fin 256) :
    d.representation (generator i) (coord p) = coord (move i p) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
  · have hi : j.castSucc.val ≠ 4 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
    simp only [generator,hi,↓reduceDIte,d.on_inner,naturalDualRepresentation_apply]
    apply Prod.ext
    · exact natural_move j p
    · apply LinearMap.ext
      intro v
      change dotProduct (bits _) (v + v (col j) • Pi.single (row j) 1) =
        dotProduct (bits _) v
      rw [dual_move]
      simp only [dotProduct_add,dotProduct_smul,dotProduct_single,add_dotProduct,
        smul_dotProduct,single_dotProduct,mul_one,one_mul]
      exact congrArg (fun t => _ + t) (mul_comm _ _)
  · simp only [generator,Fin.val_last,↓reduceDIte,d.on_graph,coordinateSwap_apply,
      coord,LinearEquiv.symm_apply_apply]
    apply Prod.ext
    · change bits _ = bits _
      apply congrArg bits
      apply Fin.ext
      change p.val % 16 = (16 * (p.val % 16) + p.val / 16) / 16
      omega
    · apply congrArg (dotProductEquiv (ZMod 2) (Fin 4))
      apply congrArg bits
      apply Fin.ext
      change p.val / 16 = (16 * (p.val % 16) + p.val / 16) % 16
      omega

theorem coord_surjective : Function.Surjective coord := by
  have hs : Function.Surjective bits := by decide +kernel
  intro v
  obtain ⟨a,ha⟩ := hs v.1
  obtain ⟨b,hb⟩ := hs ((dotProductEquiv (ZMod 2) (Fin 4)).symm v.2)
  refine ⟨⟨a.val*16+b.val, by omega⟩, ?_⟩
  have hdiv : (a.val*16+b.val)/16 = a.val := by omega
  have hmod : (a.val*16+b.val)%16 = b.val := by omega
  simp only [coord, hdiv, hmod, Fin.eta, ha, hb, LinearEquiv.apply_symm_apply]

theorem generator_fix (d : CoordinateAction 4) (i : Fin 5) (hi : i ≠ 3) :
    d.representation (generator i) (coord 17) = coord 17 := by
  rw [generator_coord]
  have he : move i 17 = 17 := by revert i; decide +kernel
  rw [he]

theorem root_reachable (d : CoordinateAction 4) (p : Fin 256) (hp : good p) :
    ∃ g ∈ fullStabilizer d (coord 17),
      d.representation g (coord (root p)) = coord p := by
  induction p using (measure depth).wf.induction with
  | h p ih =>
    rcases forest p hp with he | ⟨hq,hd,hr,hi,he⟩
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; exact congrArg coord he.symm⟩
    obtain ⟨g,hg,hgp⟩ := ih (parent p) hd hq
    refine ⟨generator (edge p) * g, Subgroup.mul_mem _ (generator_fix d _ hi) hg, ?_⟩
    rw [map_mul, Module.End.mul_apply, ← hr, hgp, generator_coord, he]

def word : Fin 256 → List (Fin 5) := fun r =>
  if r = 19 then [3] else if r = 34 then [3,4,3,4,3] else
  if r = 35 then [3,4,3] else if r = 53 then [3,0,3,4,3] else []
def wordMove : List (Fin 5) → Fin 256 → Fin 256
  | [], p => p
  | i :: is, p => move i (wordMove is p)
noncomputable def wordActor : List (Fin 5) → MulAut (LinearGroup 4)
  | [] => 1
  | i :: is => generator i * wordActor is

theorem word_coord (d : CoordinateAction 4) (is : List (Fin 5)) (p : Fin 256) :
    d.representation (wordActor is) (coord p) = coord (wordMove is p) := by
  induction is with
  | nil => rw [wordActor, map_one]; rfl
  | cons i is ih => rw [wordActor, map_mul, Module.End.mul_apply, ih, generator_coord]; rfl

private def Reach (d : CoordinateAction 4) (K : Subgroup (MulAut (LinearGroup 4)))
    (p : Fin 256) : Prop := ∃ g ∈ K, d.representation g (coord 17) = coord p

private theorem reach_root_iff (d : CoordinateAction 4)
    {K : Subgroup (MulAut (LinearGroup 4))} (hK : fullStabilizer d (coord 17) ≤ K)
    (p : Fin 256) (hp : good p) : Reach d K (root p) ↔ Reach d K p := by
  obtain ⟨g,hg,he⟩ := root_reachable d p hp
  constructor
  · rintro ⟨k,hk,hke⟩
    exact ⟨g*k,K.mul_mem (hK hg) hk, by rw [map_mul,Module.End.mul_apply,hke,he]⟩
  · rintro ⟨k,hk,hke⟩
    refine ⟨g⁻¹*k,K.mul_mem (K.inv_mem (hK hg)) hk, ?_⟩
    rw [map_mul,Module.End.mul_apply,hke,←he,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel,map_one]
    rfl

private theorem word_mem (d : CoordinateAction 4)
    {K : Subgroup (MulAut (LinearGroup 4))} (hK : fullStabilizer d (coord 17) ≤ K)
    {r : Fin 256} (hr : r = 19 ∨ r = 34 ∨ r = 35 ∨ r = 53)
    (hR : Reach d K r) : wordActor (word r) ∈ K := by
  have he : wordMove (word r) 17 = r := by rcases hr with rfl|rfl|rfl|rfl <;> decide +kernel
  obtain ⟨k,hk,hke⟩ := hR
  have hs : k⁻¹ * wordActor (word r) ∈ fullStabilizer d (coord 17) := by
    change d.representation (k⁻¹ * wordActor (word r)) (coord 17) = coord 17
    rw [map_mul,Module.End.mul_apply,word_coord,he,←hke,←Module.End.mul_apply,
      ←map_mul,inv_mul_cancel,map_one]
    rfl
  simpa only [mul_inv_cancel_left] using K.mul_mem hk (hK hs)

private theorem propagate (d : CoordinateAction 4)
    {K : Subgroup (MulAut (LinearGroup 4))} (hK : fullStabilizer d (coord 17) ≤ K)
    {r p : Fin 256} (hr : r = 19 ∨ r = 34 ∨ r = 35 ∨ r = 53)
    (hR : Reach d K r) (hp : good p) (hP : Reach d K (root p)) :
    Reach d K (root (wordMove (word r) p)) := by
  have hw := word_mem d hK hr hR
  obtain ⟨k,hk,hke⟩ := (reach_root_iff d hK p hp).mp hP
  have hgood : good (wordMove (word r) p) := by
    change quadratic (coord (wordMove (word r) p)) = 1
    rw [←word_coord d,ModelOrbits.coordinate_quadratic_invariant (Or.inl rfl)]
    exact hp
  apply (reach_root_iff d hK _ hgood).mpr
  exact ⟨wordActor (word r)*k,K.mul_mem hw hk,
    by rw [map_mul,Module.End.mul_apply,hke,word_coord]⟩

private theorem propagate_checked (d : CoordinateAction 4)
    {K : Subgroup (MulAut (LinearGroup 4))} (hK : fullStabilizer d (coord 17) ≤ K)
    (r p s t : Fin 256) (hr : r = 19 ∨ r = 34 ∨ r = 35 ∨ r = 53)
    (hp : good p) (hs : root p = s) (ht : root (wordMove (word r) p) = t)
    (hR : Reach d K r) (hS : Reach d K s) : Reach d K t := by
  rw [←ht]
  exact propagate d hK hr hR hp (hs.symm ▸ hS)

private theorem reach_all (d : CoordinateAction 4)
    {K : Subgroup (MulAut (LinearGroup 4))} (hK : fullStabilizer d (coord 17) ≤ K)
    {r : Fin 256} (hr : r = 19 ∨ r = 34 ∨ r = 35 ∨ r = 53)
    (hR : Reach d K r) : ∀ p, good p → Reach d K p := by
  have h19 : Reach d K 19 := by
    rcases hr with rfl|rfl|rfl|rfl
    · exact hR
    · exact propagate_checked d hK 34 38 34 19 (by decide) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hR hR
    · exact propagate_checked d hK 35 39 35 19 (by decide) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hR hR
    · exact propagate_checked d hK 53 211 53 19 (by decide) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hR hR
  have h35 : Reach d K 35 :=
    propagate_checked d hK 19 49 19 35 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h19 h19
  have h53 : Reach d K 53 :=
    propagate_checked d hK 19 81 19 53 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h19 h19
  have h34 : Reach d K 34 :=
    propagate_checked d hK 35 49 19 34 (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) h35 h19
  intro p hp
  apply (reach_root_iff d hK p hp).mp
  rcases roots p hp with he|he|he|he|he <;> rw [he]
  · exact ⟨1,K.one_mem,by rw [map_one]; rfl⟩
  · exact h19
  · exact h34
  · exact h35
  · exact h53

theorem base_stabilizer_isCoatom (d : CoordinateAction 4) :
    IsCoatom (fullStabilizer d (coord 17)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro he
    have hm : generator 3 ∈ fullStabilizer d (coord 17) := he ▸ Subgroup.mem_top _
    change d.representation (generator 3) (coord 17) = coord 17 at hm
    rw [generator_coord] at hm
    have hc := congrArg (fun v : CoordinateSpace 4 => v.2 (Pi.single 1 1)) hm
    exact (by decide +kernel : (coord (move 3 17)).2 (Pi.single 1 1) ≠
      (coord 17).2 (Pi.single 1 1)) hc
  · intro K hK
    obtain ⟨g,hg,hgn⟩ := SetLike.exists_of_lt hK
    obtain ⟨p,hp⟩ := coord_surjective (d.representation g (coord 17))
    have hgood : good p := by
      change quadratic (coord p) = 1
      rw [hp,ModelOrbits.coordinate_quadratic_invariant (Or.inl rfl)]
      decide +kernel
    have hpne : p ≠ 17 := by
      intro he
      apply hgn
      change d.representation g (coord 17) = coord 17
      rw [←hp,he]
    have hrne : root p ≠ 17 := fun he => hpne ((root_base p hgood).mp he)
    have hr := (roots p hgood).resolve_left hrne
    have hR := (reach_root_iff d hK.le p hgood).mpr ⟨g,hg,hp.symm⟩
    have hall := reach_all d hK.le hr hR
    apply top_unique
    intro a _
    obtain ⟨q,hq⟩ := coord_surjective (d.representation a (coord 17))
    have hqgood : good q := by
      change quadratic (coord q) = 1
      rw [hq,ModelOrbits.coordinate_quadratic_invariant (Or.inl rfl)]
      decide +kernel
    obtain ⟨k,hk,hke⟩ := hall q hqgood
    have hs : k⁻¹*a ∈ fullStabilizer d (coord 17) := by
      change d.representation (k⁻¹*a) (coord 17) = coord 17
      rw [map_mul,Module.End.mul_apply,←hq,←hke,←Module.End.mul_apply,
        ←map_mul,inv_mul_cancel,map_one]
      rfl
    simpa only [mul_inv_cancel_left] using K.mul_mem hk (hK.le hs)

end
end BinaryNaturalDual.VectorStabilizers.FourMaximal

public section
namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- Every nonsingular vector stabilizer is maximal in the full doubled action. -/
theorem four_nonsingular_stabilizer_isCoatom (d : CoordinateAction 4)
    (v : CoordinateSpace 4) (hv : quadratic v = 1) : IsCoatom (fullStabilizer d v) := by
  obtain ⟨g,hg⟩ := ModelOrbits.exists_inner_eq_of_pairing_one d
    (show quadratic (FourMaximal.coord 17) = 1 by decide +kernel) hv
  let a := MulAut.conj g
  have he : (fullStabilizer d (FourMaximal.coord 17)).map (MulAut.conj a).toMonoidHom =
      fullStabilizer d v := by
    ext b
    constructor
    · rintro ⟨c,hc,rfl⟩
      change d.representation (a*c*a⁻¹) v = v
      rw [←hg]
      change d.representation (a*c*a⁻¹) (d.representation a (FourMaximal.coord 17)) =
        d.representation a (FourMaximal.coord 17)
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right,map_mul,
        Module.End.mul_apply]
      exact congrArg (d.representation a) hc
    · intro hb
      refine ⟨a⁻¹*b*a,?_,by change a*(a⁻¹*b*a)*a⁻¹=b; group⟩
      change d.representation (a⁻¹*b*a) (FourMaximal.coord 17) = FourMaximal.coord 17
      rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hg,hb,←hg]
      change d.representation a⁻¹ (d.representation a (FourMaximal.coord 17)) = _
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
      rfl
  rw [←he]
  exact (OrderIso.isCoatom_iff (MulAut.conj a).mapSubgroup _).mpr (FourMaximal.base_stabilizer_isCoatom d)
end BinaryNaturalDual.VectorStabilizers
end
