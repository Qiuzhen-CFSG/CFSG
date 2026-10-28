module
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Aligning endpoints on whole Sylow normalizers

An isomorphism between finite endpoint groups can be corrected by inner
conjugation to identify specified Sylow normalizers. A second conjugation
inside the normalizer also matches a specified Sylow subgroup of the middle.
The original endpoint map and the actual conjugating correction are retained.

The two restrictions need not agree: their difference is an automorphism
of the whole middle, giving a compatible isomorphism to a twisted amalgam.
The I.4.5 application in G2Recognition/MaximalMiddleAlignment uses the
three-subgroup normalizers and their Sylow two-subgroup tori. This does not
assert that a twist extends to either endpoint.
-/

public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B L' B' : Type*} [Group L] [Group B] [Group L'] [Group B']

/-- Align an endpoint on the whole Sylow normalizer, retaining the conjugating correction. -/
theorem exists_normalized_normalizer_endpoint {p : ℕ} [Fact p.Prime] [Finite L']
    (i : B →* L) (j : B' →* L')
    (hi : Function.Injective i) (hj : Function.Injective j)
    (Pi : Sylow p L) (hPi : normalizer (Pi:Set L) = i.range)
    (Pj : Sylow p L') (hPj : normalizer (Pj:Set L') = j.range)
    (e : L ≃* L') :
    ∃ g : L', ∃ u : B ≃* B',
      (∀ b, (e.trans (MulAut.conj g)) (i b) = j (u b)) ∧
      (Pi:Subgroup L).map (e.trans (MulAut.conj g)).toMonoidHom = Pj := by
  let : Finite L := Finite.of_injective e e.injective
  let Q := Pi.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L' Q Pj
  let f := e.trans (MulAut.conj g)
  have hs : (Pi:Subgroup L).map f.toMonoidHom=Pj := by
    have hh := congrArg (fun P : Sylow p L'=>(P:Subgroup L')) hg
    change ((Pi:Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom=_ at hh
    simpa [f,map_map] using hh
  have hf : i.range.map f.toMonoidHom=j.range := by
    rw [←hPi]
    change (normalizer ((Pi:Subgroup L):Set L)).map f.toMonoidHom=j.range
    rw [map_equiv_normalizer_eq,hs]
    exact hPj
  let u : B ≃* B' := (MonoidHom.ofInjective hi).trans
    ((f.subgroupMap i.range).trans
      ((MulEquiv.subgroupCongr hf).trans (MonoidHom.ofInjective hj).symm))
  refine ⟨g,u,fun b=>?_,hs⟩
  exact (MonoidHom.apply_ofInjective_symm hj
    ((MulEquiv.subgroupCongr hf) ((f.subgroupMap i.range)
      (MonoidHom.ofInjective hi b)))).symm

/-- The same endpoint adjustment also matches a marked Sylow subgroup of the
whole middle, by conjugating once more inside that middle. -/
theorem exists_normalized_normalizer_endpoint_with_sylow
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite L'] [Finite B']
    (i : B →* L) (j : B' →* L')
    (hi : Function.Injective i) (hj : Function.Injective j)
    (Pi : Sylow p L) (hPi : normalizer (Pi:Set L) = i.range)
    (Pj : Sylow p L') (hPj : normalizer (Pj:Set L') = j.range)
    (Ai : Sylow q B) (Aj : Sylow q B') (e : L ≃* L') :
    ∃ g : L', ∃ u : B ≃* B',
      (∀ b, (e.trans (MulAut.conj g)) (i b) = j (u b)) ∧
      (Pi:Subgroup L).map (e.trans (MulAut.conj g)).toMonoidHom = Pj ∧
      (Ai:Subgroup B).map u.toMonoidHom=Aj := by
  obtain ⟨g,u,hu,hP⟩ := exists_normalized_normalizer_endpoint i j hi hj Pi hPi Pj hPj e
  let : Finite B := Finite.of_injective u u.injective
  let Q := Ai.mapSurjective (f:=u.toMonoidHom) u.surjective
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq B' Q Aj
  let v := u.trans (MulAut.conj a)
  have hA : (Ai:Subgroup B).map v.toMonoidHom=Aj := by
    have hh := congrArg (fun P : Sylow q B'=>(P:Subgroup B')) ha
    change ((Ai:Subgroup B).map u.toMonoidHom).map (MulAut.conj a).toMonoidHom=_ at hh
    simpa [v,map_map] using hh
  have hf : e.trans (MulAut.conj (j a*g))=
      (e.trans (MulAut.conj g)).trans (MulAut.conj (j a)) := by
    ext x
    change (j a*g)*e x*(j a*g)⁻¹=j a*(g*e x*g⁻¹)*(j a)⁻¹
    group
  refine ⟨j a*g,v,?_,?_,hA⟩
  · intro b
    rw [hf]
    change j a*((e.trans (MulAut.conj g)) (i b))*(j a)⁻¹=j (a*u b*a⁻¹)
    rw [hu,map_mul,map_mul,map_inv]
  · rw [hf]
    change (Pi:Subgroup L).map
      ((MulAut.conj (j a)).toMonoidHom.comp (e.trans (MulAut.conj g)).toMonoidHom)=_
    rw [←map_map,hP]
    apply mem_normalizer_iff_map_conj_eq.mp
    change j a∈normalizer (Pj:Set L')
    rw [hPj]
    exact ⟨a,rfl⟩

/-- The residual difference is a genuine automorphism of the entire middle. -/
def isoTwistOfEndpointSquares
    {R R' : Type*} [Group R] [Group R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (f : L ≃* L') (g : R ≃* R') (u v : B ≃* B')
    (hu : ∀ b,f (α.left b)=β.left (u b))
    (hv : ∀ b,g (α.right b)=β.right (v b)) :
    Iso α (twistRight β (u.symm.trans v)) where
  left := f
  right := g
  middle := u
  left_commutes := hu
  right_commutes b := by simpa [twistRight] using hv b

end Theory.GroupTheory.RankTwoAmalgam
