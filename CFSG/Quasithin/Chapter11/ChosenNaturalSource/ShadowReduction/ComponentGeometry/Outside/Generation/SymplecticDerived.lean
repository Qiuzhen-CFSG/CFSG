module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeFrattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Displacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.CartanFixed
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Generation one in the original prime-PSL₂ component row

In the exceptional Sp₄ block of 11.1.5, C_T(L)=1 makes the outer Sylow
core abelian. The actual radical product and O₂(L)=V then put [R₁,R₁]
inside the original seed. The natural projection is injective, so this
derived subgroup is elementary abelian of order at most q⁴. Two explicit
point-root matrices show that L₁ acts nontrivially on it.

For a hypothetical larger-generation H in the prime-PSL₂ row, K normalizes
R₁ and hence its derived subgroup. The action kernel lies in O₂(K), since
K is perfect with simple quotient and solvable kernel. At q=4 the resulting
order divisibility contradicts PrimeFrattini's small-action obstruction.
The source prime row excludes SL₃(4), and the actual block predicates exclude
G₂. Thus every original outside H has generation one in the prime row.
Together with the equality row, only the source odd SL₂ extension remains.

The exact earlier 11.1.5 alternative, comparison geometry, full 11.3.2,
surviving list and Kz=K remain inputs from the existing source producers.
OddKernelNormalizer remains with qt-d-1222-natural-odd-kernel-normalizer;
qt-d-1222-shadow-components retains final discharge of those earlier inputs.
Source: Aschbacher--Smith, 11.1.5 and 11.4.4, printed pp.765–766,778.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open LocalGeometry LocalGeometry.Normalizers LocalGeometry.Normalizers.PointCohomology
open Theory.SpecificGroups.SymplecticFour
open PointGeometry.Sp4Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

include D S m in
private theorem core_commutative (hb : CFSG.Quasithin.ChapterC.IsShort L)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    IsMulCommutative ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let a := coreCocycleHom D (.sp4 m) hb
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [coreCocycleHom_ker,hC,bot_subgroupOf]
  exact ⟨⟨fun x y => hi (by rw [map_mul,map_mul,mul_comm])⟩⟩

private theorem local_core_derived_le_seed (f : InvariantFlag (.sp4 m))
    (hb : CFSG.Quasithin.ChapterC.IsShort L) :
    ⁅(f.Li 0).pCoreIn 2,(f.Li 0).pCoreIn 2⁆ ≤ V := by
  let A := (f.Li 0).pCoreIn 2
  have hL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hA : A ≤ L := (pCoreIn_le 2 _).trans hL
  have hmodel : modelImage D S m A = ((pointLocal (F := S.field.Carrier)).pCoreIn 2).map
      (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
    rw [modelImage_core D S m _ hL,modelImage_point,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective]
  have hm : IsMulCommutative (modelImage D S m A) := by
    rw [hmodel]
    have he : (pointLocal (F := S.field.Carrier)).pCoreIn 2 =
        (pointRadical (F := S.field.Carrier)).map pointLocal.subtype := by
      rw [Subgroup.pCoreIn,pointLocal_core_eq S.field.card_eq S.nonbinary]
    rw [he]
    let : IsMulCommutative (pointRadical (F := S.field.Carrier)) :=
      (pointRadical_elementaryAbelian (F := S.field.Carrier)).toIsMulCommutative
    let : IsMulCommutative ((pointRadical (F := S.field.Carrier)).map pointLocal.subtype) :=
      Subgroup.map_isMulCommutative _ _
    exact Subgroup.map_isMulCommutative _ _
  have hzero : ⁅modelImage D S m A,modelImage D S m A⁆ = ⊥ := by
    let := hm
    exact commutator_self_eq_bot_iff.mpr hm
  have hcore := SylowNormalizer.Sp4Terminal.intrinsic_core_eq_seed D S m hb
  apply le_trans ?_ hcore.le
  have hcommL : ⁅A,A⁆ ≤ L := (commutator_mono hA hA).trans (commutator_le_self L)
  intro x hx
  let l : L := ⟨x,hcommL hx⟩
  have him : (Coordinates.sp4 m).quotientMap l ∈ ⁅modelImage D S m A,modelImage D S m A⁆ := by
    change _ ∈ ⁅(A.subgroupOf L).map (Coordinates.sp4 m).quotientMap,
      (A.subgroupOf L).map (Coordinates.sp4 m).quotientMap⁆
    rw [←map_commutator]
    apply mem_map_of_mem
    have hmem : l ∈ ⁅A,A⁆.subgroupOf L := hx
    have hxmap : (l : G) ∈ (⁅A.subgroupOf L,A.subgroupOf L⁆).map L.subtype := by
      rwa [commutator_subgroupOf_map_eq L A A hA hA]
    exact (mem_map_iff_mem L.subtype_injective).mp hxmap
  have hone : (Coordinates.sp4 m).quotientMap l = 1 := mem_bot.mp (hzero ▸ him)
  have hp : l ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact m.groupEquiv.injective (hone.trans m.groupEquiv.map_one.symm)
  exact mem_map_of_mem L.subtype hp

/-- The derived subgroup of the full point radical lies in the original
chosen seed. The outer Sylow core is retained in the radical product. -/
theorem ofFlag_sp4_radical_derived_le_seed (f : InvariantFlag (.sp4 m))
    (hb : CFSG.Quasithin.ChapterC.IsShort L)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    ⁅f.Ri 0,f.Ri 0⁆ ≤ V := by
  let A := (f.Li 0).pCoreIn 2
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := L ⊔ (T : Subgroup G)
  have hAV : ⁅A,A⁆ ≤ V := local_core_derived_le_seed D S m f hb
  have hAQ : ⁅A,Q⁆ ≤ V := (commutator_mono
    ((pCoreIn_le 2 _).trans ((localResidual_le _).trans inf_le_left)) le_rfl).trans
      (core_displacement D hb)
  have hQQ : ⁅Q,Q⁆ ≤ V := by
    have he : ⁅Q,Q⁆ = ⊥ := commutator_self_eq_bot_iff.mpr (core_commutative D S m hb hC)
    rw [he]
    exact bot_le
  have hn : J ≤ normalizer (V : Set G) := sup_le D.normalizes S.sylow_normalizes
  have hAJ : A ≤ J := ((pCoreIn_le 2 _).trans ((localResidual_le _).trans inf_le_left)).trans le_sup_left
  have hQJ : Q ≤ J := pCoreIn_le 2 _
  have hAjoin : ⁅A ⊔ Q,A⁆ ≤ V :=
    commutator_sup_le_of_relative_normal J A Q A V hn hAJ hQJ hAV (by rwa [commutator_comm])
  have hQjoin : ⁅A ⊔ Q,Q⁆ ≤ V :=
    commutator_sup_le_of_relative_normal J A Q Q V hn hAJ hQJ hAQ hQQ
  rw [PointGeometry.Sp4Core.core_product D S m f]
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal J A Q (A ⊔ Q) V hn hAJ hQJ
    (by rwa [commutator_comm]) (by rwa [commutator_comm])

/-- The original point component acts nontrivially on the derived radical.
Two point-root matrices exhibit a nonzero iterated displacement on V. -/
theorem ofFlag_sp4_component_moves_radical_derived (f : InvariantFlag (.sp4 m)) :
    ¬ f.Li 0 ≤ centralizer ((⁅f.Ri 0,f.Ri 0⁆ : Subgroup G) : Set G) := by
  let c := Coordinates.sp4 m
  let R := f.Ri 0
  let A := (f.Li 0).pCoreIn 2
  let a : Sp S.field.Carrier := (pointRadicalElement (1:S.field.Carrier) 0 0).val
  let b : Sp S.field.Carrier := (pointRadicalElement (0:S.field.Carrier) 1 0).val
  let u : Vector S.field.Carrier := Pi.single (.inr 0) 1
  have hroot (x y z : S.field.Carrier) : (pointRadicalElement x y z).val ∈ (pointLocal (F := S.field.Carrier)).pCoreIn 2 := by
    rw [Subgroup.pCoreIn,pointLocal_core_eq S.field.card_eq S.nonbinary]
    exact mem_map_of_mem pointLocal.subtype (pointRadicalElement_mem x y z)
  have himage : modelImage D S m A = ((pointLocal (F := S.field.Carrier)).pCoreIn 2).map
      (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
    change modelImage D S m ((f.Li 0).pCoreIn 2) = _
    rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),modelImage_point,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective]
  obtain ⟨r,hr,hrq⟩ := (show MulAut.conj (Sp4.alignment m) a ∈ modelImage D S m A from
    himage.symm ▸ mem_map_of_mem _ (hroot 1 0 0))
  obtain ⟨s,hs,hsq⟩ := (show MulAut.conj (Sp4.alignment m) b ∈ modelImage D S m A from
    himage.symm ▸ mem_map_of_mem _ (hroot 0 1 0))
  have hrq' : m.groupEquiv (QuotientGroup.mk' (pCore 2 L) r) =
      MulAut.conj (Sp4.alignment m) a := hrq
  have hsq' : m.groupEquiv (QuotientGroup.mk' (pCore 2 L) s) =
      MulAut.conj (Sp4.alignment m) b := hsq
  have hAR : A ≤ R := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd ((Sp4.alignment m) • u))
  let d : V := V.normalizerMonoidHom (inclusion D.normalizes r) v * v⁻¹
  have hd : (d : G) ∈ ⁅R,R⁆ :=
    commutator_mem_commutator (hAR hr) (f.seed_le_Ri S 0 v.property)
  have hproj : (c.projection d).toAdd = (Sp4.alignment m) • (a • u-u) := by
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes r) v * v⁻¹)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,c.projection_component_conjugation,hv]
    change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) r) • ((Sp4.alignment m) • u) +
      -((Sp4.alignment m) • u) = (Sp4.alignment m) • (a • u-u)
    rw [hrq']
    simp only [MulAut.conj_apply,mul_smul,inv_smul_smul]
    rw [smul_sub,sub_eq_add_neg]
  intro hcentral
  have he : V.normalizerMonoidHom (inclusion D.normalizes s) d = d := by
    apply Subtype.ext
    change (s : G) * (d : G) * (s : G)⁻¹ = d
    exact mul_inv_eq_iff_eq_mul.mpr ((hcentral ((pCoreIn_le 2 _) hs)) d hd).symm
  have hh := c.projection_component_conjugation s d
  rw [he,hproj] at hh
  change (Sp4.alignment m) • (a • u-u) = (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) s)) • ((Sp4.alignment m) • (a • u-u)) at hh
  rw [hsq'] at hh
  have hzero : a • u-u = b • (a • u-u) := by
    have h := congrArg (fun w : Vector S.field.Carrier => (Sp4.alignment m)⁻¹ • w) hh
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using h
  have hz := congrFun hzero (.inl 0)
  norm_num [a,b,u,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,
    pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Pi.single_apply,Sum.inl_ne_inr] at hz

/-- With C_T(L)=1, the central part of the original seed vanishes and
its entire derived radical has at most q⁴ elements. -/
theorem ofFlag_sp4_radical_derived_card (f : InvariantFlag (.sp4 m))
    (hb : CFSG.Quasithin.ChapterC.IsShort L)
    (hC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card (⁅f.Ri 0,f.Ri 0⁆ : Subgroup G) ≤ Nat.card S.field.Carrier ^ 4 := by
  have hfix : V ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ D.le_sylow).trans_eq hC)
  have hi : Function.Injective (Coordinates.sp4 m).projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hv
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hfix ▸ (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
      ⟨v.property,((Coordinates.sp4 m).projection_eq_one_iff v).mp hv⟩))
  have hv : Nat.card V ≤ Nat.card S.field.Carrier ^ 4 := by
    let p : V → Multiplicative ((Fin 2 ⊕ Fin 2) → S.field.Carrier) := (Coordinates.sp4 m).projection
    have hh := Nat.card_le_card_of_injective p hi
    change Nat.card V ≤ Nat.card ((Fin 2 ⊕ Fin 2) → S.field.Carrier) at hh
    simpa only [Nat.card_fun,Nat.card_sum,Nat.card_fin] using hh
  exact (card_le_of_le (ofFlag_sp4_radical_derived_le_seed D S m f hb hC)).trans hv


/-- The derived-radical action excludes the remaining prime-PSL₂ row
on the actual symplectic flag, retaining the original two-core kernel. -/
theorem ofFlag_sp4_prime_generation_eq_one
    (f : InvariantFlag (.sp4 m)) (X : Subgroup G) (z : G) (H : Subgroup G)
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
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
      pCore 2 (ofFlag S f X z H).K) 2 p) :
    ChapterE.generationParameter H = 1 := by
  by_contra hn
  have hpos := (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change 0 < ChapterE.generationParameter H at hpos
  have hlarge : 1 < ChapterE.generationParameter H := by omega
  obtain hone | ⟨hfour,_,_,hb,hC,_⟩ := ofFlag_generation_one_or_exceptional_block
    S f X z H h hcase he hlinear h1132 hcontrol hH hHz h1115
  · exact hn hone
  have hshort : CFSG.Quasithin.ChapterC.IsShort L := hb.elim (fun b => b.2.1) (fun b => b.1)
  let E := ofFlag S f X z H
  let R := f.Ri 0
  let U := ⁅R,R⁆
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hA : f.Li 0 ≠ ⊥ := by
    intro hbot
    have hlocal := Triangle.Reselection.flag_residual_mem_local D S f 0
    apply hlocal.1.ne_bot
    rw [hbot,bot_subgroupOf]
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hR := Radical.ofFlag_surviving_radical_containment S f X z H E.K hKc hA hAK
    ((f.invariant 0).trans E.G₁_normalizes_K) hcase
  have hcore := prime_radical_eq_core E h (f.invariant 0) hR (by omega : 3 < p) hm
  have hKN : E.K ≤ normalizer (R : Set G) := by
    change E.K ≤ normalizer (E.R₁ : Set G)
    rw [hcore]
    exact le_sup_left.trans ((E.K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hKU : E.K ≤ normalizer (U : Set G) := by
    have he : (_root_.commutator R).map R.subtype = U := by
      rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rw [←he]
    exact hKN.trans (normalizer_le_normalizer_characteristic_image R (_root_.commutator R))
  have hmove : ¬ E.K ≤ centralizer (U : Set G) := fun hc =>
    ofFlag_sp4_component_moves_radical_derived D S m f (hAK.trans hc)
  have hU : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.of_injective
      (inclusion (ofFlag_sp4_radical_derived_le_seed D S m f hshort hC)) (inclusion_injective _)
  have hsmall : Nat.card U ≤ 256 := by
    have hh := ofFlag_sp4_radical_derived_card D S m f hshort hC
    rw [S.field.card_eq,hfour] at hh
    exact hh
  exact ofFlag_large_generation_prime_small_action_impossible D S f X z H
    h hcase he hlinear h1132 hcontrol hH hHz hlarge hp hp7 hm U hU hsmall hKU hmove

/-- Source 11.4.4 holds for every original H in the prime-PSL₂ row,
using the exact earlier radical alternative, not a supplied size bound. -/
theorem ofFlag_prime_generation_eq_one
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
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
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
      pCore 2 (ofFlag S f X z H).K) 2 p)
    (hnotSL : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4) :
    ChapterE.generationParameter H = 1 := by
  obtain hone | ⟨hfour,_,_,hb,_,_⟩ := ofFlag_generation_one_or_exceptional_block
    S f X z H h hcase he hlinear h1132 hcontrol hH hHz h1115
  · exact hone
  cases c with
  | sl3 a =>
    exact (hnotSL ⟨S.field.Carrier,inferInstance,inferInstance,
      by rw [S.field.card_eq,hfour]; rfl,⟨a.groupEquiv⟩⟩).elim
  | sp4 a =>
    exact ofFlag_sp4_prime_generation_eq_one D S a f X z H h hcase he
      hlinear h1132 hcontrol hH hHz h1115 hp hp7 hm
  | g2 a => exact (PointGeometry.no_g2_block_marking D S a
      (by simpa only [hfour] using hb)).elim

/-- The universal generation-one problem now has only the source odd
SL₂ extension left; equality and the full prime-PSL₂ row are discharged. -/
theorem ofFlag_generation_one_or_odd_extension
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
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
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    ChapterE.generationParameter H = 1 ∨
      (S.field.degree = 2 ∧ ∃ p : ℕ, (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) ∧
        Source.IsSL (Source.TwoOddQuotient (ofFlag S f X z H).K) 2 p) := by
  cases hcase with
  | equal hk => exact Or.inl (ofFlag_equal_generation_eq_one S f X z H h he hk.symm
      hlinear h1132 hcontrol hH hHz)
  | sl2Prime _ hn p hp hm => exact Or.inr ⟨hn,p,hp,hm⟩
  | psl2Prime hi hn p hp hlarge hm hnotSL =>
    exact Or.inl (ofFlag_prime_generation_eq_one D S f X z H h
      (.psl2Prime hi hn p hp hlarge hm hnotSL) he hlinear h1132 hcontrol hH hHz h1115
      hp (by omega) hm hnotSL)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
