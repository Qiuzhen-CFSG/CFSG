module
public import Theory.Representation.G2BinaryNaturalOffenders
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# The binary natural G₂ fixed-space families

An elementary actor meeting each codimension-below-k subgroup in the same
fixed space, for k≥2, is exactly a conjugate of the actual A–B–C group and
has k=2. Its index-at-most-two intersection with G₂(2)′ consists of long
roots; simultaneous fusion bounds its fixed codimension by three. A long
root line handles rank two and excludes k≥3. The proved natural offender
classification then supplies the precise group, without enumeration.

Source: Aschbacher–Smith B.4.6(3),(9), pp.88–89, used in 13.3.19, p.896.
The hypotheses below are the literal fixed-space equalities defining A_k;
the elementary earlier bound k≤rank(A) is retained for the module consumer.
-/

@[expose] public section
noncomputable section
namespace Atlas.G2.Natural.BinaryFixedFamily
open Subgroup Representation Representation.BinaryOffender NaturalOffenders
open LieParabolicSetup ShortRootProducts
abbrev G := Model (ZMod 2)
abbrev ρ := binaryNatural (F:=ZMod 2)
abbrev D : Subgroup G := commutator G

private theorem long_of_mem_derived {b:G} (hb:b∈D) (h2:b^2=1) (h1:b≠1) :
    IsLongRootElement b := by
  rcases EvenInvolutionGeometry.involution_isRoot h2 h1 with ⟨g,a,ha,rfl⟩|⟨g,a,ha,rfl⟩
  · exact ⟨a,ha,g,rfl⟩
  · have ha1:a=1 := by
      have h := (show ∀x:ZMod 2,x=0∨x=1 by decide +kernel) a
      exact h.resolve_left ha
    subst a
    have hh:rootC (1:ZMod 2)∈D := by
      have h: g⁻¹*(g*rootC 1*g⁻¹)*g∈D :=
        (inferInstance:D.Normal).conj_mem' _ hb g
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h
    exact (BinaryNormalizer.rootC_not_mem_derived hh).elim

private theorem long_cost {b:G} (hb:IsLongRootElement b) : fixedCodim ρ (zpowers b)=2 := by
  rw [natural_fixedCodim_eq]
  exact fixedCodim_longRoot (n:=1) (by norm_num) hb

private theorem pure_cost_le_three (B:Subgroup G) (hB:IsElementaryTwo B)
    (hp:∀b∈B,b≠1→IsLongRootElement b) : fixedCodim ρ B≤3 := by
  obtain ⟨g,hg⟩:=EvenInvolutionGeometry.PureLong.exists_map_le_longRootLocal B hB.2 hp
  have hc:Nat.card B≤4 := by
    have hh:=card_le_of_le hg
    rw [card_map_of_injective (MulAut.conj g).injective,card_longRootLocal] at hh
    norm_num at hh ⊢
    exact hh
  have hr:rank B≤2 := by
    have hh:=Nat.log_mono_right (b:=2) hc
    norm_num [rank] at hh ⊢
    exact hh
  have hr1:1≤rank B := by
    have hcB:=hB.card_eq_two_pow_rank
    have hn:=B.one_lt_card_iff_ne_bot.mpr hB.1
    by_contra! hh
    have hr0:rank B=0:=by omega
    rw [hr0] at hcB
    simp only [pow_zero] at hcB
    omega
  have hcB:=hB.card_eq_two_pow_rank
  interval_cases hrank:rank B
  · norm_num only [pow_one] at hcB
    obtain ⟨b,hb,hb1⟩:=B.bot_or_exists_ne_one.resolve_left hB.1
    let : IsElementaryAbelian 2 B:=hB.2
    have ho:orderOf b=2:=orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hb1
    have he:B=zpowers b := by
      apply (eq_of_le_of_card_ge (zpowers_le.mpr hb) ?_).symm
      rw [hcB,Nat.card_zpowers,ho]
    rw [he,long_cost (hp b hb hb1)]
    decide
  · have he:B.map (MulAut.conj g).toMonoidHom=longRootLocal := by
      apply eq_of_le_of_card_ge hg
      rw [card_map_of_injective (MulAut.conj g).injective,card_longRootLocal,hcB]
      norm_num
    have h:=fixedCodim_longRootLocal (n:=1) (F:=ZMod 2) (by norm_num)
    rw [←he,fixedCodim_map_conj] at h
    rw [natural_fixedCodim_eq,h]

/-- Exact binary model classification of the source fixed-space family. -/
theorem family_shape (k:ℕ) (hk:2≤k) (A:Subgroup G) (hA:IsElementaryTwo A)
    (hrk:k≤rank A)
    (hfix:∀B≤A,Nat.log 2 (B.relIndex A)<k→fixedSpace ρ A=fixedSpace ρ B) :
    k=2 ∧ rank A=3 ∧ ∃g:G,A=(EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj g).toMonoidHom := by
  let : IsElementaryAbelian 2 A:=hA.2
  have hr3:rank A≤3 := by
    have hc:Nat.card A≤2^3 := by
      have hh:primeRank 2 G≤3:=by simpa using (EvenTwoRank.two_rank (ZMod 2) (n:=1) (by norm_num)).le
      exact (primeRank_le_iff_elementary_card_le G).mp hh A hA.2
    have hh:=Nat.log_mono_right (b:=2) hc
    simpa only [rank,Nat.log_pow (by decide:1<2)] using hh
  let B:=A⊓D
  have hBA:B≤A:=inf_le_left
  have hi:B.relIndex A≤2 := by
    have hd:D.index=2 := by
      rw [D,BinaryParabolicPair.commutator_eq_longRootClosure,BinaryException.index_H]
    rw [show B=A⊓D from rfl,inf_relIndex_left]
    have hh:=D.relIndex_dvd_index_of_normal A
    rw [hd] at hh
    exact Nat.le_of_dvd (by decide) hh
  have hfixB:fixedSpace ρ A=fixedSpace ρ B := hfix B hBA (by
    have hh:=Nat.log_mono_right (b:=2) hi
    norm_num at hh
    omega)
  have hBn:B≠⊥ := by
    intro he
    rw [he,relIndex_bot_left] at hi
    have hAc:=hA.card_eq_two_pow_rank
    have hfour:4≤Nat.card A := by
      rw [hAc]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤rank A)
    omega
  have hEB:=hA.of_le hBA hBn
  have hlong:∀b∈B,b≠1→IsLongRootElement b := by
    intro b hb hb1
    exact long_of_mem_derived hb.2 (elemPow_eq_one_of_isElementaryAbelian b (hBA hb)) hb1
  have hcost:fixedCodim ρ A≤3 := by
    change Module.finrank (ZMod 2) (_⧸fixedSpace ρ A)≤3
    rw [hfixB]
    exact pure_cost_le_three B hEB hlong
  obtain ⟨b,hb,hb1⟩:=B.bot_or_exists_ne_one.resolve_left hBn
  have hbA:b∈A:=hBA hb
  have ho:orderOf b=2:=orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hbA) hb1
  have hline:zpowers b≤A:=zpowers_le.mpr hbA
  have hlineidx:(zpowers b).relIndex A*2=2^(rank A) := by
    have hh:=relIndex_mul_card_of_le hline
    rw [Nat.card_zpowers,ho,hA.card_eq_two_pow_rank] at hh
    exact hh
  have hoff:IsOffender ρ A := by
    refine ⟨hA,?_⟩
    by_cases hr:rank A=2
    · have hidx:(zpowers b).relIndex A=2:=by rw [hr] at hlineidx;omega
      have he:=hfix _ hline (by rw [hidx];norm_num;omega)
      change Module.finrank (ZMod 2) (_⧸fixedSpace ρ A)≤rank A
      rw [he]
      change fixedCodim ρ (zpowers b)≤rank A
      rw [long_cost (hlong b hb hb1),hr]
    · omega
  have hAr:rank A=3:=by simpa using natural_offender_rank (n:=1) (by norm_num) (by decide) A hoff
  have hAcost:fixedCodim ρ A=3:=by simpa using natural_offender_fixedCodim (n:=1) (by norm_num) (by decide) A hoff
  have hk2:k=2 := by
    by_contra hk2
    have hk3:3≤k:=by omega
    have hidx:(zpowers b).relIndex A=4:=by rw [hAr] at hlineidx;omega
    have he:=hfix _ hline (by rw [hidx];norm_num;omega)
    have hc:fixedCodim ρ A=2:=by unfold fixedCodim;rw [he];exact long_cost (hlong b hb hb1)
    omega
  exact ⟨hk2,hAr,natural_offender_conjugate_elementary (n:=1) (by norm_num) (by decide) A hoff⟩
/-- The actual short-root involution moves three binary dimensions. -/
theorem short_root_cost : fixedCodim ρ (zpowers (rootC (1:ZMod 2)))=3 := by
  have he:fixedSpace (binaryAction (F:=ZMod 2)) (zpowers (rootC 1))=
      (upper (F:=ZMod 2)).restrictScalars (ZMod 2) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact fixed_rootC_iff 1 one_ne_zero v
  have h:=fixedCodim_add_finrank (binaryAction (F:=ZMod 2)) (zpowers (rootC 1))
  rw [he,upper_binary_finrank (n:=1) (by norm_num),coordinates_binary_finrank (n:=1) (by norm_num)] at h
  rw [natural_fixedCodim_eq]
  omega

/-- The classified actor contains an actual involution with displacement
rank three, the input needed for the original commutator-space bound. -/
theorem family_shape_and_displacement (k:ℕ) (hk:2≤k) (A:Subgroup G) (hA:IsElementaryTwo A)
    (hrk:k≤rank A)
    (hfix:∀B≤A,Nat.log 2 (B.relIndex A)<k→fixedSpace ρ A=fixedSpace ρ B) :
    k=2 ∧ rank A=3 ∧ ∃a∈A,orderOf a=2 ∧ fixedCodim ρ (zpowers a)=3 := by
  obtain ⟨hk2,hr,g,hg⟩:=family_shape k hk A hA hrk hfix
  let a:=MulAut.conj g (rootC (1:ZMod 2))
  have ha:a∈A := by
    rw [hg]
    exact mem_map_of_mem _ (rootC_mem_elementary 1)
  have ha1:a≠1 := by
    intro h
    have h1:rootC (1:ZMod 2)=1 := (MulAut.conj g).injective (h.trans (map_one _).symm)
    exact BinaryNormalizer.rootC_not_mem_derived (h1 ▸ D.one_mem)
  let : IsElementaryAbelian 2 A:=hA.2
  refine ⟨hk2,hr,a,ha,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1,?_⟩
  change fixedCodim ρ (zpowers ((MulAut.conj g).toMonoidHom (rootC 1)))=3
  rw [←MonoidHom.map_zpowers,fixedCodim_map_conj]
  exact short_root_cost
end Atlas.G2.Natural.BinaryFixedFamily
