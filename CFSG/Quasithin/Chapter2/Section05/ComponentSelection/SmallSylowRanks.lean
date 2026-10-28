module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import Theory.GroupTheory.PrimeRankDihedral
/-!
# Rank and involutions in the source Sylow shapes

The cyclic subgroup of index two bounds the two-rank of both source models.
Dihedral reflections give noncommuting involutions; in semidihedral order
sixteen, the reflection and its product with the square of a rotation do so.
The proofs use the defining relations, and transport through the specified
Sylow equivalences from source 2.5.8(3), printed p.556. These properties feed
the fixed-component inspection in 2.5.19, printed p.561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
private theorem dihedral_noncommuting {m:ℕ} (hm:2≤m) :
    ¬∀x y:DihedralGroup (2^m),x^2=1→y^2=1→Commute x y := by
  intro h
  have hc:=h (.sr 0) (.sr 1) (by simp [pow_two]) (by simp [pow_two])
  have hp:(DihedralGroup.r 1:DihedralGroup (2^m))^2=1 := by
    have hh:=hc.mul_pow 2
    simpa [pow_two] using hh
  have hd:=orderOf_dvd_of_pow_eq_one hp
  rw [DihedralGroup.orderOf_r_one] at hd
  have hl:4≤2^m:=Nat.pow_le_pow_right (by decide : 1≤2) hm
  have hh:=Nat.le_of_dvd (by decide:0<2) hd
  omega

private theorem semidihedral_noncommuting :
    ¬∀x y:Semidihedral.StandardModel 4 (by omega),x^2=1→y^2=1→Commute x y := by
  intro h
  let a:=Semidihedral.standardRotation 4 (by omega)
  let b:=Semidihedral.standardReflection 4 (by omega)
  have ha:a^8=1:=by
    have hh:=pow_orderOf_eq_one a
    rw [Semidihedral.standardRotation_order] at hh
    exact hh
  have hb:b^2=1:=by
    have hh:=pow_orderOf_eq_one b
    rw [Semidihedral.standardReflection_order] at hh
    exact hh
  have hc:b*a*b⁻¹=a^3:=Semidihedral.standard_conjugation 4 (by omega)
  have hc2:b*a^2*b⁻¹=a^6 := by
    have hh:=congrArg (fun x=>x^2) hc
    simpa only [←conj_pow,←pow_mul] using hh
  have hb':b*b=1:=by simpa only [pow_two] using hb
  have hc2':b*a^2=a^6*b := by
    exact (mul_inv_eq_iff_eq_mul).mp hc2
  have hsq:(a^2*b)^2=1 := by
    calc
      (a^2*b)^2=a^2*(b*a^2)*b := by simp only [pow_two, mul_assoc]
      _=a^2*(a^6*b)*b := by rw [hc2']
      _=a^8 := by simp only [mul_assoc,hb',mul_one,←pow_add]
      _=1 := ha
  have hcomm:=h b (a^2*b) hb hsq
  have he:a^6=a^2 := by
    have hh:=hcomm.eq
    rw [←mul_assoc b, hc2',mul_assoc, hb',mul_one, mul_assoc,hb',mul_one] at hh
    exact hh
  have hp:a^4=1 := by
    apply mul_left_cancel (a:=a^2)
    simpa only [←pow_add,mul_one] using he
  have hd:=orderOf_dvd_of_pow_eq_one hp
  rw [Semidihedral.standardRotation_order] at hd
  norm_num at hd

/-- Both actual Sylow models in source 2.5.8 have rank at most two and
contain two noncommuting involutions. -/
theorem SourceSylowTwoShape.rank_and_involutions {P:Type*} [Group P] [Finite P]
    (h:SourceSylowTwoShape P) : primeRank 2 P≤2 ∧
    ¬∀x y:P,x^2=1→y^2=1→Commute x y := by
  have transport {Q:Type} [Group Q] [Finite Q] (e:P≃*Q)
      (hr:primeRank 2 Q≤2) (hn:¬∀x y:Q,x^2=1→y^2=1→Commute x y) :
      primeRank 2 P≤2 ∧ ¬∀x y:P,x^2=1→y^2=1→Commute x y := by
    refine ⟨by rw [primeRank_equiv 2 e];exact hr, ?_⟩
    intro hh
    apply hn
    intro x y hx hy
    have hc:=hh (e.symm x) (e.symm y)
      (by rw [←map_pow,hx,map_one]) (by rw [←map_pow,hy,map_one])
    simpa using hc.map e.toMonoidHom
  unfold SourceSylowTwoShape at h
  rcases h with h | h
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    exact transport e (dihedral_rank_le_two m) (dihedral_noncommuting hm)
  · obtain ⟨e⟩ := h
    exact transport e (semidihedral_rank_le_two 4 (by omega)) semidihedral_noncommuting
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
