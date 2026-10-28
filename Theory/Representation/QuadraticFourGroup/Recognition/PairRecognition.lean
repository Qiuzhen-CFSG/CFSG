module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.DiagonalAssembly
public import Theory.Representation.QuadraticFourGroup.Recognition.Burnside
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows
public import Theory.GroupTheory.PCoreProduct

/-!
# The single component pair in quadratic four-group recognition

Coordinates on the actual component embeddings rule out four components:
independent involution and non-two-torsion coordinates would contradict the
odd-transposition conclusion. Burnside recognition identifies the remaining
simple quotient. Cyclic odd Sylows in the concrete factors eliminate the odd
part of the perfect central-cover kernel; the kernel is exactly the two-core.

Source: GLS volume 2, Chapter G, Theorem 25.14, Steps 2--3.
-/

public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup
universe u v
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}


namespace PairConstruction.Frame
variable {h : Hypotheses ρ L B a} (d : PairConstruction.Frame h)

omit [Finite G] in
/-- The marked actor sends the first embedded component to the second. -/
theorem marked_conjugation_embedding (i : Fin d.count) (x : L) :
    h.orbitConjugation ⟨a,h.mem⟩ (d.embedding (i,false) x) =
      d.embedding (i,true) x := by
  apply Subtype.ext
  change MulAut.conj a (MulAut.conj (d.rep i : G) (x : G)) =
    MulAut.conj (a * d.rep i) (x : G)
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- An odd-transposition actor cannot move two independent component pairs:
a product involving a quotient involution and an element not killed by two
would have even order greater than two. -/
theorem count_eq_one (hodd : HasOddTranspositions a)
    (t : L ⧸ center L) (ht : orderOf t = 2) : d.count = 1 := by
  classical
  let := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hz : ∃ z : L ⧸ center L, ¬ orderOf z ∣ 2 := by
    by_contra! hz
    exact Group.IsPerfect.not_isSolvable (L ⧸ center L)
      (Group.isSolvable_of_comm (fun x y => (Commute.of_orderOf_dvd_two hz x y).eq))
  obtain ⟨z,hz⟩ := hz
  obtain ⟨tx,htx⟩ := QuotientGroup.mk'_surjective (center L) t
  obtain ⟨zx,hzx⟩ := QuotientGroup.mk'_surjective (center L) z
  obtain ⟨e,he⟩ := centralProduct_quotient_coordinates d.embedding
    d.embedding_injective d.embedding_commute d.embedding_generate
  let ψ := e.toMonoidHom.comp (QuotientGroup.mk' (center (componentOrbit L B)))
  have hem (i : Fin d.count × Bool) (x : L) :
      ψ (d.embedding i x) = Pi.mulSingle i (QuotientGroup.mk' (center L) x) := he i x
  have hsub : Subsingleton (Fin d.count) := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    let x : componentOrbit L B := d.embedding (i,false) tx * d.embedding (j,false) zx
    let y := h.orbitConjugation ⟨a,h.mem⟩ x⁻¹ * x
    have hy : (y : G) = a * ((x : G)⁻¹ * a * (x : G)) := by
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (PairConstruction.square h)
      change a * (x : G)⁻¹ * a⁻¹ * (x : G) = _
      rw [ha]
      group
    have hψy : ψ y =
        (Pi.mulSingle (i,true) t * Pi.mulSingle (j,true) z)⁻¹ *
        (Pi.mulSingle (i,false) t * Pi.mulSingle (j,false) z) := by
      simp only [y, x, map_mul, map_inv, d.marked_conjugation_embedding, hem, htx, hzx]
    have hti : ψ y (i,false) = t := by
      rw [hψy]
      simp [hij]
    have hzj : ψ y (j,false) = z := by
      rw [hψy]
      simp [Ne.symm hij]
    have htd : 2 ∣ orderOf (y : G) := by
      have hh := orderOf_map_dvd ((Pi.evalMonoidHom _ (i,false)).comp ψ) y
      simpa only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, hti, ht, Subgroup.orderOf_coe] using hh
    have hzd : orderOf z ∣ orderOf (y : G) := by
      have hh := orderOf_map_dvd ((Pi.evalMonoidHom _ (j,false)).comp ψ) y
      simpa only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, hzj, Subgroup.orderOf_coe] using hh
    rcases hodd (x : G) with ho | ho
    · exact hz (hy ▸ hzd |> fun hh => ho ▸ hh)
    · exact ho.not_two_dvd_nat (hy ▸ htd)
  have hp := d.pos
  by_contra hn
  have hp2 : 1 < d.count := by omega
  have he := congrArg Fin.val (hsub.elim (⟨0,hp⟩ : Fin d.count) ⟨1,hp2⟩)
  exact Nat.zero_ne_one he
end PairConstruction.Frame

/-- Odd transpositions give the literal two-core quotient model once the
component quotient contains an involution. -/
theorem Hypotheses.twoFactorModel_of_oddTranspositions
    (h : Hypotheses ρ L B a) (hodd : HasOddTranspositions a)
    (t : L ⧸ center L) (ht : orderOf t = 2) :
    Nonempty (TwoFactorModel (componentOrbit L B)) := by
  classical
  let := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  obtain ⟨n,hn,⟨eS⟩⟩ := (h.quotient_spectrum hodd).recognition t ht
  obtain ⟨d⟩ := PairConstruction.frame_exists h
  have hd := d.count_eq_one hodd t ht
  have hsub : Subsingleton (Fin d.count) := by rw [hd]; infer_instance
  let := hsub
  let : Unique (Fin d.count) := ⟨⟨⟨0,d.pos⟩⟩, fun _ => Subsingleton.elim _ _⟩
  obtain ⟨e₀, _⟩ := centralProduct_quotient_coordinates d.embedding
    d.embedding_injective d.embedding_commute d.embedding_generate
  let e : componentOrbit L B ⧸ center (componentOrbit L B) ≃*
      Factor n × Factor n :=
    e₀.trans (PairConstruction.pairedEquiv.trans
      ((MulEquiv.piUnique fun _ : Fin d.count => (L ⧸ center L) × (L ⧸ center L)).trans
        (eS.prodCongr eS)))
  let := h.orbit_properties.1
  let f : componentOrbit L B →* Factor n × Factor n :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center (componentOrbit L B)))
  let c : PerfectCentralCovering.Cover (componentOrbit L B) (Factor n × Factor n) := {
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      exact e.injective (hx.trans e.map_one.symm) }
  have hk2 := c.kernel_isTwoGroup_prod (factor_oddSylow_isCyclic n)
    (factor_oddSylow_isCyclic n)
  have hc : pCore 2 (Factor n × Factor n) = ⊥ := by
    rw [pCore_prod, factor_twoCore_eq_bot, bot_prod_bot]
  have hk : c.toMonoidHom.ker = pCore 2 (componentOrbit L B) := by
    have he := c.toMonoidHom.comap_pCore_of_ker_isPGroup c.surjective hk2
    rw [hc] at he
    exact he
  exact ⟨{
    n := n
    one_lt := hn
    quotientEquiv := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.toMonoidHom c.surjective) }⟩

end Representation.QuadraticFourGroup
