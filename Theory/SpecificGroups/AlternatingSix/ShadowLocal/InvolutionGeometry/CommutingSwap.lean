module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# An involution interchanging two commuting A₆ involutions

Conjugate the first involution to a double transposition. Its four distinct
commuting involutions are interchanged with it by four explicit double
transpositions. Transport retains the supplied pair and returns a literal
involutory conjugator.
-/

public noncomputable section
namespace AlternatingSix.ShadowLocal
local notation "S" => Equiv.Perm (Fin 6)
local notation "A" => alternatingGroup (Fin 6)
private def a0 : A := ⟨Equiv.swap 0 1*Equiv.swap 2 3,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def swaps : List A :=
  [⟨Equiv.swap 0 4*Equiv.swap 1 5,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
   ⟨Equiv.swap 2 4*Equiv.swap 3 5,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
   ⟨Equiv.swap 1 2*Equiv.swap 4 5,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
   ⟨Equiv.swap 1 3*Equiv.swap 4 5,by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩]
private theorem certificate : ∀ b : S, b∈alternatingGroup (Fin 6) →
    b^2=1 → b≠1 → b≠a0.val → b*a0.val=a0.val*b →
    ∃ s∈swaps, s^2=1 ∧ s.val*a0.val*s.val⁻¹=b := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- Distinct commuting involutions in the actual alternating six admit
an involutory conjugator interchanging the same pair. -/
theorem exists_involutory_swap (a b : alternatingGroup (Fin 6)) (ha : orderOf a=2) (hb : orderOf b=2)
    (hab : Commute a b) (hne : a≠b) :
    ∃ s : alternatingGroup (Fin 6), orderOf s=2 ∧ s*a*s⁻¹=b := by
  have ha0 : orderOf a0=2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_isConj a a0 ha ha0)
  let B := g*b*g⁻¹
  have hB2 : B^2=1 := by
    change (MulAut.conj g b)^2=1
    rw [←map_pow,show b^2=1 from hb ▸ pow_orderOf_eq_one b,map_one]
  have hB1 : B≠1 := by
    intro he
    have hh : b=1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
    rw [hh,orderOf_one] at hb
    omega
  have hBa : B≠a0 := by
    intro he
    apply hne
    apply (MulAut.conj g).injective
    exact hg.trans he.symm
  have hcomm : B*a0=a0*B := by
    rw [←hg]
    exact (hab.symm.map (MulAut.conj g).toMonoidHom).eq
  obtain ⟨s,_,hs2,hs⟩ := certificate B.val B.property
    (congrArg Subtype.val hB2) (fun he => hB1 (Subtype.ext he))
    (fun he => hBa (Subtype.ext he)) (congrArg Subtype.val hcomm)
  have hsA : s*a0*s⁻¹=B := Subtype.ext hs
  let t := g⁻¹*s*g
  have ht2 : t^2=1 := by
    change (MulAut.conj g⁻¹ s)^2=1
    rw [←map_pow,hs2,map_one]
  have htconj : t*a*t⁻¹=b := by
    change (g⁻¹*s*g)*a*(g⁻¹*s*g)⁻¹=b
    calc
      _=g⁻¹*(s*(g*a*g⁻¹)*s⁻¹)*g := by group
      _=b := by rw [hg,hsA]; dsimp [B]; group
  have ht1 : t≠1 := by intro he; rw [he,one_mul,inv_one,mul_one] at htconj; exact hne htconj
  exact ⟨t,orderOf_eq_prime ht2 ht1,htconj⟩

end AlternatingSix.ShadowLocal
