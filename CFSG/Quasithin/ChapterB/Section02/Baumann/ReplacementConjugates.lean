module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.TwoConjugates
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Baumann decomposition from the constructed enlarged module

Two conjugate Thompson images generating the full quotient lift to a normal
subgroup containing the two-residual: the full two-group kernel normalizes
both Thompson subgroups. Once alpha(R)V is elementary and normalized, its
initial fixed-space supplement transports to the conjugate. The dimension
bound gives the alpha decomposition, and the two-group centralizer turns
the source Sylow conclusion into equality.

This formulation uses the actual enlarged module already proved by maximum
replacement, rather than requiring a bound on every elementary subgroup of
the quotient. The augmentation plane application discharges the elementary,
normalization, generation and dimension premises in PlaneBaumann.
Source: Aschbacher--Smith B.2.18, pp.80--81, and the line-stabilizer branch
of C.1.37, pp.142--143, used in13.2.2(10), p.878.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB.BaumannArgument
variable {G D : Type*} [Group G] [Finite G] [Group D]

omit [Finite G] in
/-- The full two-group kernel normalizes both conjugate Thompson subgroups,
so image generation lifts to containment of the actual two-residual. -/
theorem residual_le_two_thompson_conjugates
    (R : Subgroup G) (q : G →* D) (hk : IsPGroup 2 q.ker) (hQR : q.ker ≤ R)
    (g : G)
    (hgen : (elementaryAbelianMaxJ R).map q ⊔
      ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q = ⊤) :
    pResidual 2 G ≤ elementaryAbelianMaxJ R ⊔
      (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom := by
  let J := elementaryAbelianMaxJ R
  let Jg := J.map (MulAut.conj g).toMonoidHom
  let I := J ⊔ Jg
  have hQJ : q.ker ≤ normalizer (J : Set G) :=
    hQR.trans (R.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ R))
  have hQJg : q.ker ≤ normalizer (Jg : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hQJ).trans
      (J.le_normalizer_map (MulAut.conj g).toMonoidHom)
    have hq : q.ker.map (MulAut.conj g).toMonoidHom = q.ker :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top];exact mem_top g)
    rwa [hq] at hh
  have hQI : q.ker ≤ normalizer (I : Set G) :=
    (le_inf hQJ hQJg).trans (normalizer_inf_normalizer_le_normalizer_sup J Jg)
  have hcover : I ⊔ q.ker = ⊤ := by
    have hm : I.map q = ⊤ := by rw [Subgroup.map_sup];exact hgen
    have hh := congrArg (comap q) hm
    simpa only [comap_map_eq,comap_top] using hh
  let : I.Normal := normalizer_eq_top_iff.mp (top_unique (hcover ▸ sup_le I.le_normalizer hQI))
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top I q.ker hk hcover⟩

omit [Finite G] in
private theorem fixed_supplement_conjugate (V E J : Subgroup G) [V.Normal]
    (hV : V ≤ E) (hn : (⊤ : Subgroup G) ≤ normalizer (E : Set G))
    (hs : E = (E ⊓ centralizer (J : Set G)) ⊔ V) (g : G) :
    E = (E ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G)) ⊔ V := by
  let c := (MulAut.conj g).toMonoidHom
  have hE : E.map c = E := mem_normalizer_iff_map_conj_eq.mp (hn (mem_top g))
  have hVm : V.map c = V :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top];exact mem_top g)
  have hfixed : (E ⊓ centralizer (J : Set G)).map c ≤ E ⊓ centralizer (J.map c : Set G) :=
    le_inf ((map_mono inf_le_left).trans_eq hE)
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ c))
  apply le_antisymm ?_ (sup_le inf_le_left hV)
  calc E = E.map c := hE.symm
    _ = ((E ⊓ centralizer (J : Set G)) ⊔ V).map c := congrArg (map c) hs
    _ = (E ⊓ centralizer (J : Set G)).map c ⊔ V.map c := Subgroup.map_sup _ _ _
    _ ≤ (E ⊓ centralizer (J.map c : Set G)) ⊔ V := sup_le_sup hfixed hVm.le

private theorem alpha_decomposition_of_elementary_fixed_space (V R L I : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (thompsonAlpha R ⊔ V : Subgroup G)]
    (hVR : V ≤ R) (hJI : elementaryAbelianMaxJ R ≤ I)
    (hfixed : (thompsonAlpha R ⊔ V) ⊓ centralizer (L : Set G) =
      (thompsonAlpha R ⊔ V) ⊓ centralizer (I : Set G))
    (hsplit : thompsonAlpha R ⊔ V =
      ((thompsonAlpha R ⊔ V) ⊓ centralizer (L : Set G)) ⊔ V) :
    thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) := by
  let E := thompsonAlpha R ⊔ V
  let U := E ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ E from inf_le_left)
  have hUC : U ≤ centralizer (elementaryAbelianMaxJ R : Set G) := by
    change E ⊓ centralizer (L : Set G) ≤ _
    rw [hfixed]
    exact inf_le_right.trans (centralizer_le hJI)
  have hUa : U ≤ thompsonAlpha R :=
    elementary_centralizer_maxJ_le_omegaCenter R U
      (inf_le_left.trans (alpha_sup_le V R hVR)) hUC
  have hUeq : U = thompsonAlpha R ⊓ centralizer (L : Set G) :=
    le_antisymm (le_inf hUa inf_le_right) (inf_le_inf_right _ le_sup_left)
  have hFa : V ⊓ centralizer (elementaryAbelianMaxJ R : Set G) ≤ thompsonAlpha R := by
    rw [←alpha_inf_eq_fixed V R hVR]
    exact inf_le_left
  apply le_antisymm ?_ (sup_le inf_le_left hFa)
  intro a ha
  have haE : a ∈ E := (show thompsonAlpha R ≤ E from le_sup_left) ha
  rw [show E = U ⊔ V from hsplit] at haE
  obtain ⟨u,hu,v,hv,huv⟩ := mem_sup_of_normal_right.mp haE
  have hva : v ∈ thompsonAlpha R := by
    have hm := (thompsonAlpha R).mul_mem ((thompsonAlpha R).inv_mem (hUa hu)) ha
    rw [←huv] at hm
    simpa only [inv_mul_cancel_left] using hm
  have hvF : v ∈ V ⊓ centralizer (elementaryAbelianMaxJ R : Set G) := by
    rw [←alpha_inf_eq_fixed V R hVR]
    exact ⟨hva,hv⟩
  exact huv ▸ mul_mem_sup (hUeq ▸ hu) hvF

/-- The dimension and kernel conclusions of Baumann's argument from the
already constructed enlarged elementary module. Only its actual generator
codimensions are required; no all-subgroup offender bound is used. -/
theorem two_conjugate_baumann_of_enlarged_module
    (R : Subgroup G) (hQR : pCore 2 G ≤ R)
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (thompsonAlpha R ⊔ V : Subgroup G)]
    (hVR : V ≤ R) (hC : centralizer (V : Set G) = pCore 2 G)
    (hn : (⊤ : Subgroup G) ≤ normalizer ((thompsonAlpha R ⊔ V : Subgroup G) : Set G))
    (q : G →* D) (hk : q.ker = pCore 2 G) (g : G)
    (hgen : (elementaryAbelianMaxJ R).map q ⊔
      ((elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom).map q = ⊤)
    (hcod : 2 * fixedCodim V (elementaryAbelianMaxJ R) ≤ fixedCodim V (pResidual 2 G)) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      baumann R ⊓ centralizer (V : Set G) =
        (pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G) := by
  let X : Bool → Subgroup G := fun b => if b then
    (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom else elementaryAbelianMaxJ R
  have hI : (⨆ b, X b) = elementaryAbelianMaxJ R ⊔
      (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom := by
    simp only [X,iSup_bool_eq,Bool.false_eq_true,if_false,if_true,sup_comm]
  have hLI : pResidual 2 G ≤ ⨆ b, X b := hI.symm ▸
    residual_le_two_thompson_conjugates R q (hk.symm ▸ pCore_isPGroup) (hk.symm ▸ hQR) g hgen
  have hdim : (∑ b, fixedCodim V (X b)) ≤ fixedCodim V (pResidual 2 G) := by
    simpa only [X,Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,
      ChapterB.RankOneBaumann.fixedCodim_conjugate,two_mul] using hcod
  have hsupp : ∀ b, thompsonAlpha R ⊔ V =
      ((thompsonAlpha R ⊔ V) ⊓ centralizer (X b : Set G)) ⊔ V := by
    intro b
    cases b
    · exact alpha_sup_eq_fixed_sup V R
    · exact fixed_supplement_conjugate V (thompsonAlpha R ⊔ V)
        (elementaryAbelianMaxJ R) le_sup_right hn (alpha_sup_eq_fixed_sup V R) g
  obtain ⟨hfixed,hsplit⟩ := fixed_space_eq_and_supplement V (thompsonAlpha R ⊔ V)
    X (pResidual 2 G) le_sup_right (le_top.trans hn) hLI hdim hsupp
  have hd := alpha_decomposition_of_elementary_fixed_space V R (pResidual 2 G) (⨆ b, X b)
    hVR (hI.symm ▸ le_sup_left) hfixed hsplit
  have hcore : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ R ⊓ centralizer (V : Set G) := by
    have hh : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ pCore 2 G := le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
    exact le_inf (hh.trans hQR) (hh.trans_eq hC.symm)
  have hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((pResidual 2 G ⊔ R) ⊓ centralizer (V : Set G)) := by
    rw [hC,inf_eq_right.mpr hQR,inf_eq_right.mpr (hQR.trans le_sup_right)]
    obtain ⟨S,hS⟩ := (pCore_isPGroup (p := 2) (G := G)).to_subgroup (⊤ : Subgroup (pCore 2 G)) |>.exists_le_sylow
    have ht : (S : Subgroup (pCore 2 G)) = ⊤ := top_unique hS
    exact ⟨S,by simp only [ht,←MonoidHom.range_eq_map,range_subtype]⟩
  obtain ⟨S,hS⟩ := sylow_centralizer_of_decomposition V R (pResidual 2 G) hd hQ
  have hp : IsPGroup 2 ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G) : Subgroup G) :=
    (hC.symm ▸ pCore_isPGroup).to_le inf_le_right
  have ht : (S : Subgroup ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G) : Subgroup G)) = ⊤ :=
    (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  refine ⟨core_le_baumann_of_decomposition V R (pResidual 2 G) hcore hd,hd,?_⟩
  simpa only [ht,←MonoidHom.range_eq_map,range_subtype] using hS.symm
end CFSG.Quasithin.ChapterB.BaumannArgument
