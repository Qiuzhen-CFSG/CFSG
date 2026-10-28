module

public import Theory.SpecificGroups.SU3.MarkedHyperbolicCoordinates
public import Theory.GroupTheory.CyclicByFourOuterInvolutions.AmbientTransport

/-!
# Transport of a marked hyperbolic unitary plane

Equivalences carry the entire plane map and its generator markings. A
faithful homomorphism permits pullback whenever the specified inner and
Sylow subgroups are the literal images: the inverse on its range pulls
back the whole unitary plane, including every field-action identity.

For ambient Sylows, the existing four-normal-form argument first identifies
the faithful image with a full Sylow. Sylow conjugacy moves the marked plane
there. Its central inner involution is the supplied marked element by the
semidihedral centralizer calculation. The plane map can have a kernel;
only the ambient comparison homomorphism needs to be faithful.

Source application: Aschbacher--Smith E.1.14(7), p.214, A.3.21(a,b), p.55;
Aschbacher (1982), Lemma 4.11. The underlying faithful Sylow transport is
reused from `CyclicByFourOuterInvolutions.AmbientTransport`.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace Matrix.UnitaryQuaternionRotation.MarkedCyclicByFour
variable {G H F : Type*} [Group G] [Group H] [Field F]
variable {L T : Subgroup G} {z : G} {J : HermitianForm 2 F}

/-- Transport the plane map, all generator markings and the full actor action. -/
def mapEquiv (q : MarkedCyclicByFour L T z J) (e : G ≃* H) :
    MarkedCyclicByFour (L.map e.toMonoidHom) (T.map e.toMonoidHom) (e z) J where
  coordinates := {
    a := e q.coordinates.a
    b := e q.coordinates.b
    c := e q.coordinates.c
    n := q.coordinates.n
    a_order := (e.orderOf_eq q.coordinates.a).trans q.coordinates.a_order
    a_inner := mem_map_of_mem _ q.coordinates.a_inner
    a_mem := mem_map_of_mem _ q.coordinates.a_mem
    b_inner := mem_map_of_mem _ q.coordinates.b_inner
    b_mem := mem_map_of_mem _ q.coordinates.b_mem
    c_mem := mem_map_of_mem _ q.coordinates.c_mem
    c_outer := by
      rintro ⟨x, hx, he⟩
      exact q.coordinates.c_outer (e.injective he ▸ hx)
    c_sq := by rw [← map_pow, q.coordinates.c_sq, map_one]
    b_action := by simpa only [map_mul, map_pow, map_inv] using congrArg e q.coordinates.b_action
    c_action := by simpa only [map_mul, map_pow, map_inv] using congrArg e q.coordinates.c_action
    marked := by simpa only [map_pow] using congrArg e q.coordinates.marked
    cover := by
      rintro t ⟨x, hx, rfl⟩
      obtain ⟨i, hi | hi | hi | hi⟩ := q.coordinates.cover x hx
      · exact ⟨i, Or.inl (by simpa only [map_zpow, MulEquiv.coe_toMonoidHom] using congrArg e hi)⟩
      · exact ⟨i, Or.inr (Or.inl (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inl (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi)))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi)))⟩ }
  form_eq := q.form_eq
  two_ne_zero := q.two_ne_zero
  r := q.r
  r_conj := q.r_conj
  i := q.i
  i_sq := q.i_sq
  i_conj := q.i_conj
  embedding := e.toMonoidHom.comp q.embedding
  embedding_inner := fun u => mem_map_of_mem e.toMonoidHom (q.embedding_inner u)
  marker_eq := congrArg e q.marker_eq
  rotation_eq := congrArg e q.rotation_eq
  swap_eq := congrArg e q.swap_eq
  actor_action := by
    intro u
    change e q.coordinates.c * e (q.embedding u) * (e q.coordinates.c)⁻¹ =
      e (q.embedding (fieldConj J q.form_eq u))
    simpa only [map_mul, map_inv] using congrArg e (q.actor_action u)

/-- Pull a marked plane back through a faithful ambient map with the literal
inner and Sylow images. Injectivity of the plane map is unnecessary. -/
theorem of_map (f : G →* H) (hf : Function.Injective f)
    (q : MarkedCyclicByFour (L.map f) (T.map f) (f z) J) :
    Nonempty (MarkedCyclicByFour L T z J) := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let k : J.unitarySubgroup →* G := e.symm.toMonoidHom.comp
    (q.embedding.codRestrict f.range (fun u => (L.map_le_range f) (q.embedding_inner u)))
  have hk (u : J.unitarySubgroup) : f (k u) = q.embedding u :=
    congrArg Subtype.val (e.apply_symm_apply
      (⟨q.embedding u, (L.map_le_range f) (q.embedding_inner u)⟩ : f.range))
  let a := k (torus J q.form_eq q.r q.r_conj)
  let b := k (swap J q.form_eq)
  have ha : f a = q.coordinates.a := (hk _).trans q.rotation_eq
  have hb : f b = q.coordinates.b := (hk _).trans q.swap_eq
  obtain ⟨c, hcT, hc⟩ := mem_map.mp q.coordinates.c_mem
  have pull {D : Subgroup G} {x : G} (hx : f x ∈ D.map f) : x ∈ D := by
    obtain ⟨y, hy, he⟩ := mem_map.mp hx
    exact hf he ▸ hy
  let d : CyclicByFourCoordinates L T z := {
    a := a
    b := b
    c := c
    n := q.coordinates.n
    a_order := (orderOf_injective f hf a).symm.trans (ha ▸ q.coordinates.a_order)
    a_inner := pull (ha ▸ q.coordinates.a_inner)
    a_mem := pull (ha ▸ q.coordinates.a_mem)
    b_inner := pull (hb ▸ q.coordinates.b_inner)
    b_mem := pull (hb ▸ q.coordinates.b_mem)
    c_mem := hcT
    c_outer := fun h => q.coordinates.c_outer (hc ▸ mem_map_of_mem f h)
    c_sq := hf (by simpa only [map_pow, map_one, hc] using q.coordinates.c_sq)
    b_action := hf (by simpa only [map_mul, map_inv, map_pow, ha, hb]
      using q.coordinates.b_action)
    c_action := hf (by simpa only [map_mul, map_inv, map_pow, ha, hc]
      using q.coordinates.c_action)
    marked := hf (by simpa only [map_pow, ha] using q.coordinates.marked)
    cover := by
      intro t ht
      obtain ⟨i, hi | hi | hi | hi⟩ := q.coordinates.cover (f t) (mem_map_of_mem f ht)
      · exact ⟨i, Or.inl (hf (by simpa only [map_zpow, ha] using hi))⟩
      · exact ⟨i, Or.inr (Or.inl (hf (by simpa only [map_mul, map_zpow, ha, hb] using hi)))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inl (hf (by simpa only [map_mul, map_zpow, ha, hc] using hi))))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (hf (by simpa only [map_mul, map_zpow, ha, hb, hc] using hi))))⟩ }
  refine ⟨{
    coordinates := d
    form_eq := q.form_eq
    two_ne_zero := q.two_ne_zero
    r := q.r
    r_conj := q.r_conj
    i := q.i
    i_sq := q.i_sq
    i_conj := q.i_conj
    embedding := k
    embedding_inner := fun u => pull (by rw [hk]; exact q.embedding_inner u)
    marker_eq := hf ((hk _).trans q.marker_eq)
    rotation_eq := rfl
    swap_eq := rfl
    actor_action := ?_ }⟩
  intro u
  apply hf
  simpa only [d, map_mul, map_inv, hc, hk] using q.actor_action u

/-- Realize the marked plane in a faithful ambient Sylow with an outer element,
retaining the originally supplied centralizing inner involution. -/
theorem of_faithful_sylow [Finite H] (f : G →* H) (hf : Function.Injective f)
    (N : Subgroup H) [N.Normal] (hLN : L.map f = N)
    (S₀ : Sylow 2 H) {v : H} (q : MarkedCyclicByFour N (S₀ : Subgroup H) v J)
    (T : Sylow 2 G) (hout : ¬ (T : Subgroup G) ≤ L)
    (hz : orderOf z = 2) (hzL : z ∈ L) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nonempty (MarkedCyclicByFour L (T : Subgroup G) z J) := by
  obtain ⟨S, _, hS, _⟩ := q.coordinates.sylow_image_coordinates f hf N hLN S₀ T hout
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₀ S
  have hN : N.map (MulAut.conj g).toMonoidHom = N := Normal.conj_smul_eq_self g N
  have hS₀ : (S₀ : Subgroup H).map (MulAut.conj g).toMonoidHom = (S : Subgroup H) := by
    change ((g • S₀ : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  let w := MulAut.conj g v
  have qS : MarkedCyclicByFour N (S : Subgroup H) w J := by
    simpa only [hN, hS₀] using q.mapEquiv (MulAut.conj g)
  have hzw : f z = w := by
    apply qS.coordinates.eq_marked_of_inner_involution
    · rw [← hLN]; exact mem_map_of_mem f hzL
    · rw [← hS]; exact mem_map_of_mem f hzT
    · exact (orderOf_injective f hf z).trans hz
    · have haS : qS.coordinates.a ∈ (T : Subgroup G).map f := by
        rw [hS]; exact qS.coordinates.a_mem
      obtain ⟨a, ha, hae⟩ := mem_map.mp haS
      rw [← hae]
      exact (show Commute z a from (mem_centralizer_singleton_iff.mp (hTz ha)).symm).map f
  apply of_map f hf
  simpa only [hLN, hS, hzw] using qS

end Matrix.UnitaryQuaternionRotation.MarkedCyclicByFour
