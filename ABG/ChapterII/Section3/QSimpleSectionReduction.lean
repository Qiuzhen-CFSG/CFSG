module
public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import ABG.ChapterII.Section3.QOddCoreQuotient
public import ABG.ChapterII.Section2.SylowShapeTransport
public import ABG.ChapterII.Section3.SylowCenter
public import ABG.ChapterII.Section3.CentralSylowQQuotient
public import GorensteinWalter.NormalSL2ProjectiveImage
public import GorensteinWalter.IndexTwoLinearEnvelope
public import Theory.GroupTheory.SimpleSectionTransfer

/-!
# Full-shape Q simple sections occur in the prescribed PSL2 group

An even-order nonsolvable simple section of a finite Q-group with
semidihedral or wreathed Sylow two-subgroups occurs as a section of PSL2
over the field of the group's source characteristic power. All section
data are actual subgroup surjections; no centrality of their kernels is
assumed. The field of order three is retained throughout the reduction.

First remove the odd core and the central cyclic Sylow center. The given
characteristic SL2 subgroup maps to its actual PSL2 central quotient.
Gorenstein--Walter gives a normal odd-index PSL2/PGL2 envelope, whose field
order is fixed by normal-core uniqueness. Even simple sections move into
the odd-index subgroup. In the PGL2 case nonsolvability moves the section
into its derived PSL2 subgroup. These steps prove the structural reduction
in ABG II.3 Lemma2, article p24, without using the later Proposition3.
-/

namespace ABG
open GorensteinWalter
universe u v

private theorem section_equiv {A B T : Type*} [Group A] [Group B] [Group T]
    (e : A ≃* B) (U : Subgroup A) (f : U →* T) (hf : Function.Surjective f) :
    ∃ W : Subgroup B, ∃ g : W →* T, Function.Surjective g := by
  let eU := Subgroup.equivMapOfInjective U e.toMonoidHom e.injective
  exact ⟨U.map e.toMonoidHom, f.comp eU.symm.toMonoidHom, hf.comp eU.symm.surjective⟩

public theorem qGroup_simple_section_in_psl2
    {G : Type u} [Group G] [Finite G] (hQ : IsQGroup G)
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (q : ℕ) (hq : HasSourceQCharacteristicPower G q)
    {T : Type v} [Group T] [IsSimpleGroup T]
    (hTtwo : 2 ∣ Nat.card T) (hTns : ¬ Group.IsSolvable T)
    (U : Subgroup G) (f : U →* T) (hf : Function.Surjective f) :
    ∃ (E : Type u) (iE : Field E) (_ : Finite E),
      let : Field E := iE
      IsOddPrimePower (Nat.card E) ∧ Nat.card E = q ∧
        ∃ W : Subgroup (PSL2 E), ∃ g : W →* T, Function.Surjective g := by
  let O := pPrimeCore 2 G
  let H := G ⧸ O
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨U0, f0, hf0⟩ := Subgroup.simple_section_quotient_of_odd_or_solvable
    hTtwo hTns O (Or.inl hOodd) U f hf
  let R := S.mapSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  obtain ⟨eS⟩ := sylow_quotient_equiv S O pPrimeCore_coprime_card
  have hR : Stellmacher.IsSemidihedralGroup R ∨ IsWreathedGroup R := by
    rcases hS with hS | ⟨n, hS⟩
    · exact Or.inl (semidihedral_equiv eS hS)
    · exact Or.inr ⟨n, wreathed_equiv eS hS⟩
  have hQH : IsQGroup H := hQ.oddCore_quotient
  have hcore : pPrimeCore 2 H = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2)
  have hcentral : subgroupCenter (R : Subgroup H) ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hQH R
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  obtain ⟨Z, hZN, hZ, hZcyc, _hZne, hdih, hquotcore, K, hKN, hKi, _hKno⟩ :=
    qGroup_central_sylow_quotient_data hQH R hR hcentral hcore
  let : Z.Normal := hZN
  let : K.Normal := hKN
  have hZsolv : Group.IsSolvable Z := by
    let : IsCyclic Z := hZcyc
    let : CommGroup Z := IsCyclic.commGroup
    infer_instance
  obtain ⟨U1, f1, hf1⟩ := Subgroup.simple_section_quotient_of_odd_or_solvable
    hTtwo hTns Z (Or.inr hZsolv) U0 f0 hf0
  obtain ⟨F, iF, fF, hF, hFq, M, hMc, ⟨eM⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  let : M.Characteristic := hMc
  let Mbar := M.map (QuotientGroup.mk' Z)
  have hMbarN : Mbar.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  let : Mbar.Normal := hMbarN
  obtain ⟨eMbar⟩ := normal_sl2_projective_image R Z M (hZ ▸ hcentral) hZ.symm.le F hF eM
  obtain ⟨E, iE, fE, hE, hEF, N, hNN, hNi, hNm⟩ :=
    exists_normal_linear_odd_index_of_psl2_core hdih hquotcore K hKi F hF Mbar eMbar
  let : Field E := iE
  let : Finite E := fE
  let : N.Normal := hNN
  have hNquot : Odd (Nat.card ((H ⧸ Z) ⧸ N)) := by
    rwa [← N.index_eq_card]
  obtain ⟨U2, f2, hf2⟩ := Subgroup.simple_section_normal_of_quotient_odd_or_solvable
    hTtwo hTns N (Or.inl hNquot) U1 f1 hf1
  refine ⟨E, iE, fE, hE, hEF.trans hFq, ?_⟩
  rcases hNm with e | e
  · exact section_equiv e.some U2 f2 hf2
  · let : Finite (PGL2 E) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
    obtain ⟨U3, f3, hf3⟩ := section_equiv e.some U2 f2 hf2
    let C := commutator (PGL2 E)
    have hCsolv : Group.IsSolvable ((PGL2 E) ⧸ C) := by
      let : IsMulCommutative ((PGL2 E) ⧸ C) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
      exact Group.isSolvable_of_comm (fun a b => IsMulCommutative.is_comm.comm a b)
    obtain ⟨U4, f4, hf4⟩ := Subgroup.simple_section_normal_of_quotient_odd_or_solvable
      hTtwo hTns C (Or.inr hCsolv) U3 f3 hf3
    exact section_equiv (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 E hE (MulEquiv.refl _)).some
      U4 f4 hf4

end ABG
