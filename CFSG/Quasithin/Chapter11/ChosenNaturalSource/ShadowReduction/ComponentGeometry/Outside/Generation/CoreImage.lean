module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Contained
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeResidual
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import GorensteinWalter.LinearRingEquiv

/-!
# The exact core and remaining A₅ residual in the original outside H

The contained-component reduction gives R₁≤O₂(H). The prime radical model
puts the reverse inclusion in rad(KT), whose original Sylow intersection
is R₁; hence O₂(H)=R₁. The actual escaping component is normal in H,
so its T-conjugate span is itself and it equals the embedded O²(H).

Its literal radical quotient is prime PSL₂ or A₅. The first possibility
above five has generation at most one by PrimeResidual, while PSL₂(5)
is transported through the actual exceptional isomorphism. Thus any H
with n(H)>1 has an A₅ radical quotient. Selection applies this alternative
to the original chosen flag and preserves both O² residual alternatives.
The remaining A₅ exclusion and universal 11.4.4 stay with this owner.

Earlier geometry, fixed spaces, 11.3.2 and component equality retain
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison.
OddKernelNormalizer remains with qt-d-1222-natural-odd-kernel-normalizer;
qt-d-1222-shadow-components owns final discharge of these source inputs.
Source: Aschbacher--Smith 11.4.1(3), 11.4.4 and 11.5.1,
printed pp.775--779 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Large generation determines the exact original two-core as R₁. -/
theorem ofFlag_large_generation_core_eq_radical
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    H.pCoreIn 2 = f.Ri 0 := by
  have hl := ofFlag_large_generation_radical_le_core S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz hn
  apply le_antisymm ?_ hl
  obtain ⟨I,hIH,hI,hlocal,hout,hjoin,hres,hIK⟩ :=
    ofFlag_large_generation_component_le S f X z H h he hlinear h1132 hcontrol hH hHz hn
  let E := ofFlag S f X z H
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hTK := (f.invariant 0).trans E.G₁_normalizes_K
  have hIn : I ≠ ⊥ := by
    intro hh
    exact hout (hh ▸ bot_le)
  let : Group.IsPerfect I := Radical.relative_component_perfect ⟨hIH,hI⟩
  have hR : H.pCoreIn 2 ≤
      (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
        (E.K ⊔ (T : Subgroup G)).subtype := by
    cases hcase with
    | equal hEq =>
      exact (hout (hIK.trans (hEq.symm ▸ (LocalGeometry.localResidual_le _).trans (inf_le_left.trans L.le_normalizer)))).elim
    | sl2Prime _ _ p hp hm =>
      have hp' : p.Prime ∧ 3 < p := by
        rcases hp with rfl | ⟨hp,hl⟩
        · exact ⟨by decide,by decide⟩
        · exact ⟨hp,by omega⟩
      let : Fact p.Prime := ⟨hp'.1⟩
      rw [←hjoin]
      exact Radical.local_core_le_radical_of_prime_model T I E.K hIn hIK hTK hp'.2
        (Radical.relative_radical_model_of_twoOdd_sl2 h.line_component hp'.2 hm)
    | psl2Prime _ _ p hp hpbig hm _ =>
      let : Fact p.Prime := ⟨hp⟩
      let : Group.IsPerfect E.K := Radical.relative_component_perfect h.line_component
      rw [←hjoin]
      exact Radical.local_core_le_radical_of_prime_model T I E.K hIn hIK hTK (by omega)
        (Radical.radical_model_of_psl2 (by omega) hm)
  have hPT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hmap : (T.subtype hH.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) := by
      change ((T : Subgroup G).subgroupOf H).map H.subtype = _
      exact map_subgroupOf_eq_of_le hH.1.1.2
    exact (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq hmap
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hSyl := Radical.ofFlag_surviving_sylow_radical S f X z H E.K hKc hAK hTK hcase
  have hi := Radical.sylow_inf_radical_eq_local_core T (f.Li 0) E.K hAK
    (Radical.ofFlag_seed_radical_eq_core S f) (Chapter1.isSylowIn_iff.mp hSyl).2.1
  exact (le_inf hPT hR).trans_eq hi

/-- Every hypothetical outside H of larger generation has exactly the first
radical as its two-core and a normal escaping two-residual. Its actual
radical quotient is prime PSL₂ or A₅. -/
theorem ofFlag_large_generation_component_structure
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    S.field.degree = 2 ∧ H.pCoreIn 2 = f.Ri 0 ∧
    ∃ I : Subgroup G, I ≤ H ∧ (I.subgroupOf H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ normalizer (L : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ I ≤ (ofFlag S f X z H).K ∧
      (I.subgroupOf H).Normal ∧ I = (pResidual 2 H).map H.subtype ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
          solvableRadical (ofFlag S f X z H).K) 2 p ∧
        (ClassicalGroup.IsPSL (I ⧸ solvableRadical I) 2 p ∨
          Nonempty ((I ⧸ solvableRadical I) ≃* alternatingGroup (Fin 5))) := by
  obtain ⟨I,hIH,hI,hlocal,hout,hjoin,hres,hIK⟩ :=
    ofFlag_large_generation_component_le S f X z H h he hlinear h1132 hcontrol hH hHz hn
  let E := ofFlag S f X z H
  obtain ⟨p,hp,hp3,hm⟩ : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ClassicalGroup.IsPSL (E.K ⧸ solvableRadical E.K) 2 p := by
    cases hcase with
    | equal hEq =>
      exact (hout (hIK.trans (hEq.symm ▸ (LocalGeometry.localResidual_le _).trans
        (inf_le_left.trans L.le_normalizer)))).elim
    | sl2Prime _ _ p hp hm =>
      have hp' : p.Prime ∧ 3 < p := by
        rcases hp with rfl | ⟨hp,hl⟩
        · exact ⟨by decide,by decide⟩
        · exact ⟨hp,by omega⟩
      let : Fact p.Prime := ⟨hp'.1⟩
      exact ⟨p,hp'.1,hp'.2,
        Radical.relative_radical_model_of_twoOdd_sl2 h.line_component hp'.2 hm⟩
    | psl2Prime _ _ p hp hpbig hm _ =>
      let : Fact p.Prime := ⟨hp⟩
      let : Group.IsPerfect E.K := Radical.relative_component_perfect h.line_component
      exact ⟨p,hp,by omega,Radical.radical_model_of_psl2 (by omega) hm⟩
  let : Fact p.Prime := ⟨hp⟩
  have htop : (⊤ : Subgroup E.K).IsCComponent := by
    simpa only [subgroupOf_self] using
      h.line_component.2.subgroupOf_of_le le_rfl h.line_component.1
  have hTK := (f.invariant 0).trans E.G₁_normalizes_K
  have hnormal := component_normal_of_prime_radical_model E.K H I htop hTK hH.1.1.2
    (by rw [← hjoin]; exact sup_le_sup_right hIK _) hI hp3 hm
  have hHN : H ≤ normalizer (I : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIH).mp hnormal
  have horbit : conjugateSpanBy I (T : Subgroup G) = I :=
    le_antisymm (conjugateSpanBy_le le_rfl (hH.1.1.2.trans hHN))
      (le_conjugateSpanBy _ _)
  let : Group.IsPerfect I := Radical.relative_component_perfect ⟨hIH,hI⟩
  exact ⟨ofFlag_large_generation_field_four S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn,
    ofFlag_large_generation_core_eq_radical S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn,
    I,hIH,hI,hlocal,hout,hjoin,hIK,hnormal,horbit.symm.trans hres,p,hp,hp3,hm,
    perfect_subgroup_radical_prime_models I E.K (fun hh => hout (hh ▸ bot_le)) hIK hp3 hm⟩

private theorem psl_five_is_alternating_five
    {J : Type*} [Group J] (hm : ClassicalGroup.IsPSL J 2 5) :
    Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨e.trans ((GorensteinWalter.psl2RingEquiv eF).trans e5)⟩

/-- Large generation leaves only an actual A₅ radical quotient of the
normal escaping two-residual. The full prime-PSL₂ alternative is discharged
by E.1.14 and solvable-kernel lifting, on the original H carrier. -/
theorem ofFlag_large_generation_alternating_five
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    S.field.degree = 2 ∧ H.pCoreIn 2 = f.Ri 0 ∧
    ∃ I : Subgroup G, I ≤ H ∧ (I.subgroupOf H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ normalizer (L : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ I ≤ (ofFlag S f X z H).K ∧
      (I.subgroupOf H).Normal ∧ I = (pResidual 2 H).map H.subtype ∧
      Nonempty ((I ⧸ solvableRadical I) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hdeg,hcore,I,hIH,hI,hlocal,hout,hjoin,hIK,hnormal,hres,p,hp,hp3,hmK,hmI⟩ :=
    ofFlag_large_generation_component_structure S f X z H h hcase he
      hlinear h1132 hcontrol hH hHz hn
  refine ⟨hdeg,hcore,I,hIH,hI,hlocal,hout,hjoin,hIK,hnormal,hres,?_⟩
  rcases hmI with hmI | hmI
  · by_cases hp5 : 5 < p
    · let : (I.subgroupOf H).Normal := hnormal
      let ei := subgroupOfEquivOfLe hIH
      let er := QuotientGroup.congr (solvableRadical (I.subgroupOf H))
        (solvableRadical I) ei (map_solvableRadical_equiv ei)
      have hg : I.subgroupOf H ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ := by
        change I.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
        rw [← subgroupOf_sup hIH hH.1.1.2,hjoin,subgroupOf_self]
      have hb := generation_le_one_of_prime_radical_component (T.subtype hH.1.1.2)
        (I.subgroupOf H) hI hg hp hp5 (hmI.of_mulEquiv er)
      omega
    · have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      have hp5' : p = 5 := by omega
      exact psl_five_is_alternating_five (hp5' ▸ hmI)
  · exact hmI

/-- Select the original H with its literal O² alternative. The only remaining
large-generation case has two-core R₁ and a normal A₅ radical quotient of
its escaping two-residual; no quotient or component is chosen abstractly. -/
theorem ofFlag_selected_generation_alternating_alternative
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
 :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      (ChapterE.generationParameter J = 1 ∨
        (S.field.degree = 2 ∧ J.pCoreIn 2 = f.Ri 0 ∧
          let I := (pResidual 2 J).map J.subtype
          (I.subgroupOf J).IsCComponent ∧ (I.subgroupOf J).Normal ∧
          I ∈ Chapter1.L G (T : Subgroup G) ∧
          ¬ I ≤ normalizer (L : Set G) ∧ I ≤ (ofFlag S f X z J).K ∧
          Nonempty ((I ⧸ solvableRadical I) ≃* alternatingGroup (Fin 5)))) := by
  obtain ⟨J,hJ,hJz,hsel⟩ := Models.ofFlag_surviving_selected_H S f X z H h hcase he hNT h1132
  have hgeom : Comparison.EarlierGeometry (ofFlag S f X z J) :=
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
  refine ⟨J,hJ,hJz,hsel,?_⟩
  by_cases hn : ChapterE.generationParameter J = 1
  · exact Or.inl hn
  · have hp := (selected_generation_spec (ofFlag S f X z J) hgeom hJ hJz).1
    change 1 ≤ ChapterE.generationParameter J at hp
    obtain ⟨hdeg,hcore,I,hIJ,hI,hlocal,hout,hjoin,hIK,hnormal,hres,hm⟩ :=
      ofFlag_large_generation_alternating_five S f X z J hgeom hcase he
        hlinear h1132 hcontrol hJ hJz (by omega)
    refine Or.inr ⟨hdeg,hcore,?_⟩
    dsimp only
    rw [←hres]
    exact ⟨hI,hnormal,hlocal,hout,hIK,hm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
