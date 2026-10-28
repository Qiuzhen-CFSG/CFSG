module
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SixLetterPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlane
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction

/-!
# Quotients and residues of the original solvable vertices

The actual augmentation action of LT has kernel O₂(LT) and image containing
A₆. When M=LT its image is A₆ or S₆. In either case the six-letter lattice
classifies the original centralizer M∩C_G(z) and plane normalizer as the
two parabolics. Their S₃ quotients ensure that they strictly contain T.

For the third vertex, its L₃(2) quotient forces nontrivial two-core because
it contains the original V of order 32. The already constructed line
residue fixes P∩B=T. The binary linear-three lattice then gives the third
residue on these very subgroups. OriginalChamber applies these statements
to H₀=⟨IT,N_LT(V₂)⟩ and discharges the geometric hypotheses.

Source: Aschbacher–Smith 13.4.9, printed p.906. The third quotient is an
explicit earlier-amalgam input; it is not inferred from a family label.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3 Quasithin.I5
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The original augmentation action identifies the first vertex quotient;
no abstract six-letter family label is used. -/
theorem normalizer_quotient_of_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃*
      alternatingGroup (Fin 6)) ∨
    Nonempty ((normalizer (L : Set G) ⧸ pCore 2 (normalizer (L : Set G))) ≃*
      Equiv.Perm (Fin 6)) := by
  rw [hM]
  obtain ⟨q,_,_,him,hker⟩ := Nonsolvable.exists_core_product_permutation D m h structural eL
  have hA : alternatingGroup (Fin 6) ≤ q.range := him ▸ (L.subgroupOf _).map_le_range q
  have hd := index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hd
  let eq : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃* q.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange q)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr ⟨eq.trans ((MulEquiv.subgroupCongr (index_eq_one.mp hi)).trans topEquiv)⟩
  · exact Or.inl ⟨eq.trans (MulEquiv.subgroupCongr
      (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))⟩

/-- An S₃ two-core quotient prevents a Sylow overgroup from being a two-group. -/
theorem not_twoGroup_of_symmetricThree_quotient {A : Type*} [Group A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 A := by
  intro hp
  have hq := (hp.to_quotient (pCore 2 A)).of_equiv e
  obtain ⟨n,hn⟩ := hq.exists_card_eq
  have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at hd
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The first-vertex residue is constructed from the literal centralizer
and inside plane normalizer, using the actual six-letter quotient. -/
theorem original_point_parabolics
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G)) (hTB : (T : Subgroup G) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hB : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let M := normalizer (L : Set G)
    Quasithin.I5.RankTwoParabolics M ((T : Subgroup G).subgroupOf M)
      ((centralizer ({z.val} : Set G)).subgroupOf M) (B.subgroupOf M) := by
  let M := normalizer (L : Set G)
  let A := centralizer ({z.val} : Set G) ⊓ M
  let Ai := (centralizer ({z.val} : Set G)).subgroupOf M
  let Bi := B.subgroupOf M
  let S := T.subtype D.sylow_normalizes_component
  have hTA : (T : Subgroup G) ≤ A :=
    le_inf (original_sylow_le_centralizer hz) D.sylow_normalizes_component
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eA⟩ := normalizer_centralizer_quotient D m hcore z hzL hinter
  let a : Ai ≃* A :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_right _ _).symm).trans
      (subgroupOfEquivOfLe (show A ≤ M from inf_le_right))
  have ha : ¬ IsPGroup 2 Ai := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eA (hp.of_equiv a)
  let b := subgroupOfEquivOfLe hBM
  have hb : ¬ IsPGroup 2 Bi := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eB (hp.of_equiv b)
  have hSA : (S : Subgroup M) ≤ Ai := fun _ hx => (hTA hx).1
  have hSB : (S : Subgroup M) ≤ Bi := fun _ hx => hTB hx
  have hAp : Ai ≠ ⊤ := by
    intro he
    apply hzL
    intro l hl
    exact mem_centralizer_singleton_iff.mp
      (show (⟨l,L.le_normalizer hl⟩ : M) ∈ Ai from he ▸ mem_top _)
  have hne : Ai ≠ Bi := by
    intro he
    have hAB : A = B := by
      have hh := congrArg (map M.subtype) he
      rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM] at hh
    have hgen' : A ⊔ B = M := hgen
    have hBtop : B = M := by simpa only [hAB,sup_idem] using hgen'
    exact hB.ne_top (by change B.subgroupOf M = ⊤; rw [hBtop,subgroupOf_self])
  exact Quasithin.I5.RankTwoParabolics.of_six_letter_two_quotient (pCore 2 M) pCore_isPGroup
    (normalizer_quotient_of_ordinary h structural D m eL hM) S Ai Bi
    (lt_iff_le_not_ge.mpr ⟨hSA,fun hh => ha (S.isPGroup'.to_le hh)⟩)
    (lt_iff_le_not_ge.mpr ⟨hSB,fun hh => hb (S.isPGroup'.to_le hh)⟩)
    hAp hB.ne_top hne


omit [Finite G] in
/-- The literal third vertex has nontrivial two-core: its quotient has
order 168, whereas it contains the original subgroup V of order 32. -/
theorem third_vertex_local_of_linear_quotient
    (D : ChosenModule T L V) (m : CoreMarking D)
    (X : Subgroup G) (hTX : (T : Subgroup G) ≤ X)
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) : X ∈ Chapter1.H G := by
  intro hz
  have hc : Nat.card (pCore 2 X) = 1 := by
    have hh : Nat.card (X.pCoreIn 2) = 1 := hz ▸ card_bot
    rwa [pCoreIn,card_map_of_injective X.subtype_injective] at hh
  have hX : Nat.card X = 168 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X),Nat.card_congr eX.toEquiv,
      Matrix.PSL3Two.card_PSL,hc,mul_one]
  have hd := card_dvd_of_le (D.le_sylow.trans hTX)
  rw [m.card_module,hX] at hd
  norm_num at hd

/-- The original line residue fixes the chamber in the third vertex.
Its L₃(2) quotient then constructs the plane residue on B and P. -/
theorem third_vertex_parabolics
    (M H P B X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hPH : P ≤ H) (hBM : B ≤ M) (hPX : P ≤ X) (hBX : B ≤ X)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hl : Quasithin.I5.RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
      (M.subgroupOf H) (P.subgroupOf H)) :
    P ⊓ B = (T : Subgroup G) ∧
      Quasithin.I5.RankTwoParabolics X ((T : Subgroup G).subgroupOf X)
        (B.subgroupOf X) (P.subgroupOf X) := by
  have hPM : P ⊓ M = (T : Subgroup G) := by
    apply le_antisymm ?_ (le_inf hTP hTM)
    intro x hx
    exact hl.borel_eq.le (show (⟨x,hPH hx.1⟩ : H) ∈ M.subgroupOf H ⊓ P.subgroupOf H
      from ⟨hx.2,hx.1⟩)
  have hi : P ⊓ B = (T : Subgroup G) :=
    le_antisymm ((inf_le_inf_left P hBM).trans hPM.le) (le_inf hTP hTB)
  let S := T.subtype (hTP.trans hPX)
  have hni (A : Subgroup G) (hAX : A ≤ X)
      (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
      ¬ IsPGroup 2 (A.subgroupOf X) := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eA (hp.of_equiv (subgroupOfEquivOfLe hAX))
  have hp := hni P hPX eP
  have hb := hni B hBX eB
  have hii : B.subgroupOf X ⊓ P.subgroupOf X = (S : Subgroup X) := by
    change (B ⊓ P).subgroupOf X = (S : Subgroup X)
    rw [inf_comm B P,hi]
    rfl
  have hBp : B.subgroupOf X ≠ ⊤ := by
    intro he
    have hh : P.subgroupOf X = (S : Subgroup X) := by simpa only [he,top_inf_eq] using hii
    exact hp (hh ▸ S.isPGroup')
  have hPp : P.subgroupOf X ≠ ⊤ := by
    intro he
    have hh : B.subgroupOf X = (S : Subgroup X) := by simpa only [he,inf_top_eq] using hii
    exact hb (hh ▸ S.isPGroup')
  exact ⟨hi,Quasithin.I5.RankTwoParabolics.of_psl_two_quotient (pCore 2 X) pCore_isPGroup
    eX S _ _ hBp hPp hb hp hii⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
