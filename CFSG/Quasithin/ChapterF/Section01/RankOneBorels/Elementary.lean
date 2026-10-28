module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import Theory.SpecificGroups.Suzuki.SylowCommutator
public import Theory.SpecificGroups.Suzuki.SmallSylowFrattini
public import Theory.SpecificGroups.SU3.SylowFrattini
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary Sylow subgroups in the characteristic-two rank-one catalogue

In every Suzuki or unitary row, the first omega of a Sylow two-subgroup
lies in its Frattini subgroup. An elementary Sylow would therefore be
trivial, contradicting the proper Sylow normalizer. For nonbinary Suzuki
this uses the actual derived-equals-omega identity; Sz(2) uses its cyclic
order-four Sylow. Both unitary covers and all positive fixed-field degrees
are retained. Thus only PSL2(2^n) and D10 remain.

This is the model-selection step used with the literal edge-core quotients
in DGS (11.5) and (11.7). It does not assume or prove that either source
edge quotient is elementary. Conversely the linear and dihedral rows have
elementary Sylows, giving the Suzuki-or-unitary split for a nonelementary
Sylow without choosing between PSU3 and SU3.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.1)--(5.4), (11.5), (11.7), printed pp.100--105,172,174--175.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source

private theorem elementary_sylow_omega_not_le_frattini {H : Type*} [Group H] [Finite H]
    (M : IsRankOneModel H) (T : Sylow 2 H) [IsElementaryAbelian 2 T] :
    ¬ omegaOneAmbient (T : Subgroup H) ≤ (frattini T).map (T : Subgroup H).subtype := by
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  intro hh
  rw [omegaOneAmbient_eq_self,frattini_eq_bot_of_isElementaryAbelian (p := 2) (R := T),Subgroup.map_bot] at hh
  have he : (T : Subgroup H) = ⊥ := bot_unique hh
  have hn := (M.rankOneSylowFacts T).proper
  change normalizer ((T : Subgroup H) : Set H) < ⊤ at hn
  rw [he] at hn
  exact hn.ne ((⊥ : Subgroup H).normalizer_eq_top)

/-- A characteristic-two rank-one model with elementary Sylow two-subgroups
is linear or dihedral-ten, including all small parameters and both unitary covers. -/
theorem IsRankOneModel.linear_or_dihedral_of_elementary_sylow
    {H : Type*} [Group H] (M : IsRankOneModel H)
    (T : Sylow 2 H) [IsElementaryAbelian 2 T] :
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL H 2 (2^n)) ∨ Nonempty (H ≃* DihedralGroup 5) := by
  let : Finite H := M.finite
  have exclude {D : Type} [Group D] (e : H ≃* D)
      (hd : ∀ R : Sylow 2 D, omegaOneAmbient (R : Subgroup D) ≤
        (frattini R).map (R : Subgroup D).subtype) : False := by
    let : Finite D := Finite.of_surjective e e.surjective
    let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
    let : IsElementaryAbelian 2 R := IsElementaryAbelian.map e.toMonoidHom
    exact elementary_sylow_omega_not_le_frattini (M.of_equiv e.symm) R (hd R)
  cases M with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | dihedral he => exact Or.inr he
  | suzuki m he =>
    obtain ⟨e⟩ := he
    apply False.elim
    apply exclude e
    intro R
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact smallSuzuki_omega_le_frattini R
    · rw [←suzukiSylow_commutator_eq_omega hm (MulEquiv.refl _) R,←map_subtype_commutator]
      let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
      exact map_mono (commutator_le_frattini_of_isPGroup (p := 2) (R := R))
  | projective_unitary n hn he =>
    obtain ⟨K,_,_,J,hcard,hconj,⟨e⟩⟩ := he
    exact (exclude e (HermitianForm.SylowFrattini.projective_omega_le_frattini J hn hcard hconj)).elim
  | special_unitary n hn he =>
    obtain ⟨K,_,_,J,hcard,hconj,⟨e⟩⟩ := he
    exact (exclude e (HermitianForm.SylowFrattini.special_omega_le_frattini J hn hcard hconj)).elim

/-- A genuine binary linear marking makes each Sylow two-subgroup elementary. -/
theorem linear_model_sylow_elementary {H : Type*} [Group H]
    {n : ℕ} (h : ClassicalGroup.IsPSL H 2 (2^n)) (T : Sylow 2 H) :
    IsElementaryAbelian 2 T := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := h
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let ep : Matrix.SpecialLinearGroup (Fin 2) k ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let : Finite H := Finite.of_injective e e.injective
  let f := e.trans ep.symm
  let R := T.mapSurjective (f := f.toMonoidHom) f.surjective
  let et : T ≃* R := (T : Subgroup H).equivMapOfInjective f.toMonoidHom f.injective
  let ec := (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).trans et.symm
  let : IsElementaryAbelian 2 (Multiplicative k) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro x
        change 2 • x.toAdd = 0
        rw [nsmul_eq_mul,CharP.cast_eq_zero k 2,zero_mul]) }
  exact IsElementaryAbelian.of_surjective ec.toMonoidHom ec.surjective

/-- The order-ten row has elementary Sylow two-subgroups. -/
theorem dihedral_model_sylow_elementary {H : Type*} [Group H]
    (e : H ≃* DihedralGroup 5) (T : Sylow 2 H) : IsElementaryAbelian 2 T := by
  let : Finite H := Finite.of_injective e e.injective
  have hc : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    decide +kernel
  let : IsCyclic T := isCyclic_of_prime_card hc
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := by simpa only [hc] using (Group.exponent_dvd_nat_card (G := T)) }

/-- A non-elementary Sylow leaves exactly Suzuki or either genuine unitary
cover; this is the model split at the start of (11.8), including small fields. -/
theorem IsRankOneModel.suzuki_or_unitary_of_nonElementary_sylow
    {H : Type*} [Group H] (M : IsRankOneModel H)
    (T : Sylow 2 H) (hne : ¬ IsElementaryAbelian 2 T) :
    (∃ m, Nonempty (H ≃* SuzukiMatrixGroup m)) ∨
      ∃ n, 0 < n ∧ (ClassicalGroup.IsPSU H 3 (2^n) ∨ IsSU H 3 (2^n)) := by
  cases M with
  | linear n hn he => exact (hne (linear_model_sylow_elementary he T)).elim
  | dihedral he => exact (hne (dihedral_model_sylow_elementary he.some T)).elim
  | suzuki m he => exact Or.inl ⟨m,he⟩
  | projective_unitary n hn he => exact Or.inr ⟨n,hn,Or.inl he⟩
  | special_unitary n hn he => exact Or.inr ⟨n,hn,Or.inr he⟩
end CFSG.Quasithin.ChapterF.Source
