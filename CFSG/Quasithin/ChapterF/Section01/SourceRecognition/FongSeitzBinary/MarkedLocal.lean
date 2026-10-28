module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SimpleSocle

/-!
# Source local factors on an independently marked finite quotient

An isomorphism of the original inclusion amalgam with the two marked
standard parabolics identifies the whole original Borel with the actual
quotient Borel. Both commuting squares identify the two copies of S and
of the local Borels. Thus the original factors and the same S image
generate the quotient, and the S image is its specified unipotent Sylow U.
Full U normalizes each factor image. Both original perfect factors then
generate exactly the perfect two-residual, and the carrier-general
simple-socle reduction makes that residual simple.

The numerator of the marked quotient is independent of the source carrier.
In particular it can be the infinite universal completion, using the
geometricMarkedIso supplied by the apartment construction; no descent
homomorphism to the actual generated source group is assumed. Local
characteristic two and all rank-one Sylow-normalizer facts are transported
from F.1.1, not added as reduction hypotheses. The quotient, splitness and
marking remain the genuine earlier geometric inputs. This does not prove
full Fong–Seitz minimality or any of the seven marked Lie comparisons.

Source: DGS, Groups and Graphs, Part II, pp.77–81 and224;
Aschbacher–Smith F.1.1–3 and F.1.9, pp.259–261.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- Either original endpoint, with the given orientation retained. -/
@[expose] def endpoint (i : Fin 2) : parabolic L S i ≃* Q.tits.standardParabolic {Q.simple i} :=
  Fin.cases e.left (Fin.cases e.right (fun j => Fin.elim0 j)) i

/-- Embed an original endpoint in the finite marked quotient. -/
@[expose] def endpointMap (i : Fin 2) : parabolic L S i →* X ⧸ Q.D :=
  (Q.tits.standardParabolic {Q.simple i}).subtype.comp (endpoint Q e i).toMonoidHom

/-- The original local factor follows its corresponding endpoint map. -/
@[expose] def factorMap (i : Fin 2) : L i →* X ⧸ Q.D :=
  (endpointMap Q e i).comp (inclusion (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left))

/-- The common Borel follows the middle map on the entire overlap. -/
@[expose] def borelMap (h : HypothesisF11 L S) : commonBorel L S →* X ⧸ Q.D :=
  Q.tits.B.subtype.comp
    ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).toMonoidHom

/-- The original common Sylow follows the same middle map. -/
@[expose] def sylowMap (h : HypothesisF11 L S) : S →* X ⧸ Q.D :=
  (borelMap Q e h).comp (inclusion (show S ≤ commonBorel L S from le_sup_right))

private theorem standard_left (b : Q.tits.B) :
    (Q.standardAmalgam.left b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.left_commutes]
  rw [Q.markedIso_left_apply, Q.markedIso_middle_apply]
  rfl

private theorem standard_right (b : Q.tits.B) :
    (Q.standardAmalgam.right b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.right_commutes]
  rw [Q.markedIso_right_apply, Q.markedIso_middle_apply]
  rfl

/-- Both endpoint markings agree with the same full-overlap Borel map. -/
theorem endpoint_borel (h : HypothesisF11 L S) (i : Fin 2)
    (b : commonBorel L S) :
    endpointMap Q e i ⟨b, commonBorel_le_parabolic i b.property⟩ = borelMap Q e h b := by
  fin_cases i
  · exact (congrArg Subtype.val (e.left_commutes
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b))).trans (standard_left Q _)
  · exact (congrArg Subtype.val (e.right_commutes
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b))).trans (standard_right Q _)

/-- The original Sylow uses that same endpoint and overlap marking. -/
theorem endpoint_sylow (h : HypothesisF11 L S) (i : Fin 2) (s : S) :
    endpointMap Q e i ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
      sylowMap Q e h s := endpoint_borel Q e h i
        ⟨s, (show S ≤ commonBorel L S from le_sup_right) s.property⟩

private theorem factor_borel (h : HypothesisF11 L S) (i : Fin 2)
    (b : commonBorel L S) (hb : (b : G) ∈ L i) :
    factorMap Q e i ⟨b, hb⟩ = borelMap Q e h b := endpoint_borel Q e h i b

/-- The original common Sylow maps to the specified unipotent group. -/
theorem sylow_range (h : HypothesisF11 L S) (split : SplitData Q.tits) :
    (sylowMap Q e h).range = split.U := by
  let C := commonBorel L S
  let b : C ≃* Q.tits.B :=
    (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
  let := h.finite_commonBorel
  obtain ⟨T, hT⟩ := h.sylow_commonBorel
  have hT' : (T : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hT, map_subgroupOf_eq_of_le (show S ≤ C from le_sup_right)]
  let Tbar := T.mapSurjective (f := b.toMonoidHom) b.surjective
  let U := split.U.subgroupOf Q.tits.B
  let : U.Normal := normal_subgroupOf_of_le_normalizer split.normalizes
  have hU : IsPGroup 2 U := split.isTwo.comap_subtype
  have hTU : (Tbar : Subgroup Q.tits.B) = U :=
    (hU.toSylow split.borel_index_not_two).is_maximal' Tbar.isPGroup'
      (hU.le_sylow_of_normal Tbar)
  have heq := congrArg (Subgroup.map Q.tits.B.subtype) hTU
  change ((T : Subgroup C).map b.toMonoidHom).map Q.tits.B.subtype = _ at heq
  rw [map_map, hT', map_subgroupOf_eq_of_le split.U_le] at heq
  rw [← heq]
  change ((borelMap Q e h).comp (inclusion _)).range = _
  rw [MonoidHom.range_comp, inclusion_range]
  rfl

/-- Full U normalizes each original factor image. -/
theorem unipotent_normalizes (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) : split.U ≤ normalizer ((factorMap Q e i).range : Set (X ⧸ Q.D)) := by
  rw [← sylow_range Q e h split]
  intro s hs
  obtain ⟨s, rfl⟩ := hs
  rw [← endpoint_sylow Q e h i s]
  have hn : (⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ : parabolic L S i) ∈
      normalizer ((L i).subgroupOf (parabolic L S i) : Set (parabolic L S i)) :=
    (L i).le_normalizer_comap (parabolic L S i).subtype (h.S_normalizes i s.property)
  have hm := (le_normalizer_map (endpointMap Q e i)) (mem_map_of_mem _ hn)
  simpa only [factorMap, MonoidHom.range_comp, inclusion_range] using hm

/-- The two original factor images and the same S image generate the quotient. -/
theorem factors_generate (h : HypothesisF11 L S) :
    (factorMap Q e 0).range ⊔ (factorMap Q e 1).range ⊔
      (sylowMap Q e h).range = ⊤ := by
  let A := (factorMap Q e 0).range ⊔ (factorMap Q e 1).range ⊔ (sylowMap Q e h).range
  have hA (i : Fin 2) : (factorMap Q e i).range ≤ A := by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hB : (borelMap Q e h).range ≤ A := by
    rintro _ ⟨b, rfl⟩
    have hc : commonBorel L S ≤
        ((A.comap (borelMap Q e h)).map (commonBorel L S).subtype) := by
      apply sup_le
      · apply sup_le
        · intro x hx
          refine ⟨⟨x, (show borel (L 0) S ≤ commonBorel L S from le_sup_left.trans le_sup_left) hx⟩, ?_, rfl⟩
          change borelMap Q e h _ ∈ A
          rw [← factor_borel Q e h 0 _ (borel_le _ _ hx)]
          exact hA 0 ⟨_, rfl⟩
        · intro x hx
          refine ⟨⟨x, (show borel (L 1) S ≤ commonBorel L S from le_sup_right.trans le_sup_left) hx⟩, ?_, rfl⟩
          change borelMap Q e h _ ∈ A
          rw [← factor_borel Q e h 1 _ (borel_le _ _ hx)]
          exact hA 1 ⟨_, rfl⟩
      · intro x hx
        refine ⟨⟨x, (show S ≤ commonBorel L S from le_sup_right) hx⟩, ?_, rfl⟩
        exact (show (sylowMap Q e h).range ≤ A from le_sup_right) ⟨⟨x,hx⟩, rfl⟩
    obtain ⟨c, hc, he⟩ := hc b.property
    have : c = b := Subtype.ext he
    subst c
    exact hc
  have hP (i : Fin 2) : Q.tits.standardParabolic {Q.simple i} ≤ A := by
    have hh : parabolic L S i ≤
        (A.comap (endpointMap Q e i)).map (parabolic L S i).subtype := by
      nth_rw 1 [parabolic_eq_sup_commonBorel]
      apply sup_le
      · intro x hx
        exact ⟨⟨x, (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) hx⟩, hA i ⟨⟨x,hx⟩,rfl⟩, rfl⟩
      · intro x hx
        refine ⟨⟨x, commonBorel_le_parabolic i hx⟩, ?_, rfl⟩
        change endpointMap Q e i _ ∈ A
        rw [endpoint_borel Q e h i ⟨x,hx⟩]
        exact hB ⟨⟨x,hx⟩,rfl⟩
    intro y hy
    obtain ⟨x, hx⟩ := (endpoint Q e i).surjective ⟨y,hy⟩
    obtain ⟨z, hz, he⟩ := hh x.property
    have he' : z = x := Subtype.ext he
    change endpointMap Q e i z ∈ A at hz
    rw [he'] at hz
    change ((endpoint Q e i) x : X ⧸ Q.D) ∈ A at hz
    have hx' : ((endpoint Q e i) x : X ⧸ Q.D) = y := congrArg Subtype.val hx
    rw [hx'] at hz
    exact hz
  apply top_unique
  rw [← Q.tits.standardParabolic_S]
  apply Q.tits.standardParabolic_le A
  · exact (Q.tits.B_le_standardParabolic {Q.simple 0}).trans (hP 0)
  · intro s hs
    obtain ⟨i, rfl⟩ := Q.simple_range ▸ hs
    exact (Q.tits.bruhatCell_subset_standardParabolic_of_mem (by simp)).trans (hP i)


include e

/-- Local characteristic two passes through both marked endpoint equivalences. -/
theorem parabolic_core_selfCentralizing (h : HypothesisF11 L S) (i : Fin 2) :
    centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}) := by
  let := h.finite_parabolic i
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (endpoint Q e i)).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i))

private theorem factor_perfect (hp : ∀ i, Group.IsPerfect (L i)) (i : Fin 2) :
    Group.IsPerfect (factorMap Q e i).range := by
  let := hp i
  exact Group.IsPerfect.ofSurjective (factorMap Q e i).rangeRestrict_surjective

/-- The actual unipotent conjugates generate the finite geometric carrier. -/
theorem unipotentClosure_eq_top (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (split : SplitData Q.tits) :
    split.unipotentClosure = ⊤ :=
  split.unipotentClosure_eq_top_of_generation (fun i => (factorMap Q e i).range)
    (sylowMap Q e h).range (factor_perfect Q e hp)
    (h.S_isP.of_surjective _ (sylowMap Q e h).rangeRestrict_surjective)
    (factors_generate Q e h)

/-- The original factor images generate exactly the perfect two-residual. -/
theorem perfect_residual (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (split : SplitData Q.tits) :
    pResidual 2 (X ⧸ Q.D) = (factorMap Q e 0).range ⊔ (factorMap Q e 1).range ∧
      Group.IsPerfect (pResidual 2 (X ⧸ Q.D)) := by
  let A (i : Fin 2) := (factorMap Q e i).range
  let K := A 0 ⊔ A 1
  have hgen : K ⊔ split.U = ⊤ := by
    rw [← sylow_range Q e h split]
    exact factors_generate Q e h
  have hpK : Group.IsPerfect K := by
    rw [isPerfect_iff]
    apply le_antisymm K.commutator_le_self
    apply sup_le
    · let := factor_perfect Q e hp 0
      exact (A 0).commutator_eq_self.symm.le.trans
        (commutator_mono le_sup_left le_sup_left)
    · let := factor_perfect Q e hp 1
      exact (A 1).commutator_eq_self.symm.le.trans
        (commutator_mono le_sup_right le_sup_right)
  let := hpK
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le K.le_normalizer ((le_inf (unipotent_normalizes Q e h split 0)
      (unipotent_normalizes Q e h split 1)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))))
  have hr := (residuals_of_perfect_normal_sup_twoGroup K split.U split.isTwo hgen).1
  exact ⟨hr, hr.symm ▸ hpK⟩

/-- Simplicity of the residual needs only the original marked local groups,
not a homomorphism from their actual ambient generated carrier. -/
theorem twoResidual_isSimple (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (split : SplitData Q.tits) :
    IsSimpleGroup (pResidual 2 (X ⧸ Q.D)) := by
  let := h.finite_local 0
  let := hp 0
  let : Nontrivial (L 0) := (L 0).nontrivial_iff_ne_bot.mpr
    (ne_bot_of_gt (h.rankOneBorelFacts 0).proper)
  let f := factorMap Q e 0
  have hf : Function.Injective f :=
    (Q.tits.standardParabolic {Q.simple 0}).subtype_injective.comp
      ((endpoint Q e 0).injective.comp (inclusion_injective _))
  have hfK : f.range ≤ pResidual 2 (X ⧸ Q.D) := by
    rw [(perfect_residual Q e h hp split).1]
    exact le_sup_left
  obtain ⟨T, hT⟩ := h.sylow 0
  have hTU : (T : Subgroup (L 0)).map f ≤ split.U := by
    rw [← sylow_range Q e h split]
    rintro _ ⟨t, ht, rfl⟩
    have hs : (t : G) ∈ S := (hT.le (mem_map_of_mem (L 0).subtype ht)).1
    refine ⟨⟨t, hs⟩, ?_⟩
    exact (endpoint_sylow Q e h 0 ⟨t,hs⟩).symm
  have facts := rankOneSylowFacts_of_rankOneQuotient (h.quotient 0) T
  exact Q.twoResidual_isSimple_of_local_factor split (parabolic_core_selfCentralizing Q e h)
    (unipotentClosure_eq_top Q e h hp split) (perfect_residual Q e h hp split).2
    f hf hfK (unipotent_normalizes Q e h split 0) T hTU
    facts.proper facts.unique_maximal facts.solvable

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
