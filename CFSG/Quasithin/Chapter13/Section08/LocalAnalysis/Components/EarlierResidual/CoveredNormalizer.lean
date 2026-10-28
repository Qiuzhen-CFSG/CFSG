module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.CoveredKernel
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import CFSG.Quasithin.Chapter13.Section07.CoveredElimination
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.LocalSetup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.Source
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
/-!
# The covered point-residual normalizer and the original residual source

Write P = L₁T, R = O₂(P) and Q = O₂(LT). The point radical R fixes the
cubic center of L/O₂(L). Hence its action on the natural six-letter
module contains no transposition: such an automorphism of the triple
cover would invert that center. After transporting the prescribed line
to the pair {4,5}, every best offender in the point core contains the
point transposition. Thus every maximal elementary abelian subgroup of
R centralizes V, and J(R) ≤ Q ≤ R gives J(R) = J(Q).

The maximal-local hypothesis controls the normalizer of J(Q). The
normalizer-core factorization then controls N_G(L₁); its section
centralizer normalizes L₀ because L₀ is two-perfect. This discharges the
last premise of the covered centralizer-kernel argument and yields all
ordinary and covered clauses of 13.3.9 on the literal residual action.
The final Fitting application removes its earlier-source parameter;
its separate solvable-overgroup exclusion retains its original input.

Source: Aschbacher--Smith, 13.2.2(8)--(9), printed pp.877--878;
13.3.9, p.887; and the 13.8.14 application, pp.950--952.
-/

public section
section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)

omit [Finite G] in
private theorem sectionCentralizer_normalizes_residual
    (X Z : Subgroup G) (hZX : Z ≤ X) (hp : IsPPerfect 2 Z)
    (hn : X.pCoreIn 2 ≤ normalizer (Z : Set G)) :
    twoSectionCentralizer X (normalizer (X : Set G)) ≤ normalizer (Z : Set G) := by
  let Q := X.pCoreIn 2
  let C := twoSectionCentralizer X (normalizer (X : Set G))
  have hCQ : C ≤ normalizer (Q : Set G) :=
    (twoSectionCentralizer_le_normalizer _ _).trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hCZQ : C ≤ normalizer ((Z ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc z hz
    have hm : (Z ⊔ Q).map (MulAut.conj c).toMonoidHom ≤ Z ⊔ Q := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨z,hz,rfl⟩
        have hcomm : ⁅c,z⁆ ∈ Q := hc.2.2 z (hZX hz)
        have hh := (Z ⊔ Q).mul_mem (mem_sup_right hcomm) (mem_sup_left hz)
        change c*z*c⁻¹ ∈ Z ⊔ Q
        simpa only [commutatorElement_def, mul_assoc,
          inv_mul_cancel, mul_one] using hh
      · rintro _ ⟨q,hq,rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hCQ hc) q).mp hq)
    exact hm (mem_map_of_mem (MulAut.conj c).toMonoidHom hz)
  have he : residual (Z ⊔ Q) = Z :=
    embedded_pResidual_join_pGroup Z Q hp (isPGroup_pCoreIn 2 X) hn
  rw [←he]
  exact hCZQ.trans (normalizer_le_residual_normalizer _)

include d h

theorem covered_sectionCentralizer_le
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    twoSectionCentralizer (one L (T:Subgroup G) V₁)
      (normalizer (one L (T:Subgroup G) V₁ : Set G)) ≤ M := by
  obtain ⟨a⟩ := Section03.PointResidualImage.covered_flag_of_triple d hc
  have hf := SourceCompletion.CoverFactorization.source_factorization a
  have hQ : (one L (T:Subgroup G) V₁).pCoreIn 2 ≤ T :=
    (isPGroup_pCoreIn 2 _).le_sylow_of_normalized T
      ((T_normalizes_one L _ V₁ d.line_stable).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (sectionCentralizer_normalizes_residual _ _
    (zero_le_one_of_factorization L _ V₁ hf) (isPPerfect_embedded_pResidual 2 _)
    (hQ.trans (d.normalizes_L.trans (normalizer_le_zero_normalizer L)))).trans
      (SourceCompletion.SolvableSource.covered_normalizer_source d h ⟨a.cover⟩)

theorem covered_one_normalizer_of_core_normalizer
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hR : normalizer ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2 : Set G) ≤ M) :
    normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M := by
  have hf := normalizer_core_factorization T (one L (T:Subgroup G) V₁)
    (show IsPPerfect 2 (one L (T:Subgroup G) V₁) from isPPerfect_embedded_pResidual 2 _)
    (T_normalizes_one L _ V₁ d.line_stable)
  exact hf.symm.le.trans (sup_le (covered_sectionCentralizer_le d h hc) (inf_le_right.trans hR))

omit d h in
private theorem normalizer_le_thompson_normalizer (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ChapterB.thompsonJ S 0 : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (ChapterB.thompsonJ S 0).map (MulAut.conj g).toMonoidHom = _
  rw [←ChapterB.thompsonJ_map_equiv (MulAut.conj g)]
  exact congrArg (fun B => ChapterB.thompsonJ B 0)
    (show S.map (MulAut.conj g).toMonoidHom = S from mem_normalizer_iff_map_conj_eq.mp hg)

theorem covered_core_normalizer_of_thompson
    (hJ : ChapterB.thompsonJ ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2) 0 =
      ChapterB.thompsonJ ((L ⊔ (T:Subgroup G)).pCoreIn 2) 0) :
    normalizer ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2 : Set G) ≤ M := by
  let X := L ⊔ (T:Subgroup G)
  let Q := X.pCoreIn 2
  have hXQ : X ≤ normalizer (Q : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hVQ : V ≤ Q := by
    let := SourceCompletion.local_elementary d
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      ((SourceCompletion.localChosenModule d).le_sylow.trans le_sup_right) d.normalizes_V
  have hJne : ChapterB.thompsonJ Q 0 ≠ ⊥ := by
    rw [ChapterB.thompsonJ_zero]
    obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty Q
    let := SourceCompletion.local_elementary d
    have hV : IsElementaryAbelian 2 V₁ := IsElementaryAbelian.of_le
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    have hc : 2 ≤ Nat.card A := by
      rw [←d.line_card]
      exact hA.2.2 V₁
        ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans hVQ) hV
    intro he
    have hAb : A = ⊥ := bot_unique ((le_sSup hA).trans_eq he)
    rw [hAb,card_bot] at hc
    omega
  have hcontrol : normalizer (ChapterB.thompsonJ Q 0 : Set G) ≤ M := by
    rw [d.local_normalizer]
    exact h.normal_subgroup_normalizer_le d.normalizes_L
      ((ChapterB.thompsonJ_le Q 0).trans (pCoreIn_le 2 X)) hJne
      (hXQ.trans (normalizer_le_thompson_normalizer Q))
  apply (normalizer_le_thompson_normalizer _).trans
  rw [hJ]
  exact hcontrol

theorem covered_one_normalizer_of_thompson
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hJ : ChapterB.thompsonJ ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2) 0 =
      ChapterB.thompsonJ ((L ⊔ (T:Subgroup G)).pCoreIn 2) 0) :
    normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M :=
  covered_one_normalizer_of_core_normalizer d h hc (covered_core_normalizer_of_thompson d h hJ)

theorem source_of_covered_thompson
    (hJ : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      ChapterB.thompsonJ ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2) 0 =
        ChapterB.thompsonJ ((L ⊔ (T:Subgroup G)).pCoreIn 2) 0) :
    SolvableExclusion.Residual.Source1339 L (one L (T:Subgroup G) V₁)
      (plus L (T:Subgroup G) V₁) T M V V₁ := by
  apply source_of_covered_kernel d h
  intro hc J Y hJY hYJ hp hn hv
  exact covered_centralizer_kernel d h hc (covered_one_normalizer_of_thompson d h hc (hJ hc))
    hJY hYJ hp hn hv

theorem whole_residual_of_covered_thompson
    (hJ : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      ChapterB.thompsonJ ((one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G)).pCoreIn 2) 0 =
        ChapterB.thompsonJ ((L ⊔ (T:Subgroup G)).pCoreIn 2) 0)
    {H : Subgroup G} (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ (T:Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) :
    Components.Fitting.ResidualAlternatives H L (one L T V₁) (plus L T V₁) :=
  SourceCompletion.LocalFitting.whole_residual d hH (source_of_covered_thompson d h hJ) hex
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
end
section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion Section07 Section07.NaturalAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T:Subgroup G) : Subgroup G)
local notation "P" => (one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G) : Subgroup G)
local notation "R" => Subgroup.pCoreIn 2 P
local notation "s" => localNaturalSetup d
include d

private theorem point_product_eq : P = parabolic L (T:Subgroup G) V₁ :=
  TransvectionQuotients.FiveSeed.BarMarking.residual_normalizer_sup_sylow
    X V₁ T le_sup_right d.line_stable

private theorem centralCore_le_point : (centralCore L).map L.subtype ≤ P := by
  rw [point_product_eq d]
  refine le_inf ((map_subtype_le _).trans le_sup_left) ?_
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  apply le_trans _ (centralizer_le (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)))
  rintro _ ⟨l,hl,rfl⟩
  rwa [d.centralCore_eq_centralizer] at hl

omit [Finite G] d in
private theorem point_core_le_sylow : R ≤ T :=
  (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T
    (le_sup_right.trans ((P).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))

private theorem point_core_fixes_center (x : X) (hx : x.val ∈ R)
    (z : L ⧸ pCore 2 L) (hz : z ∈ center (L ⧸ pCore 2 L)) :
    source_quotient_action s x z = z := by
  let C := (centralCore L).map L.subtype
  let : (centralCore L).Characteristic :=
    inferInstanceAs (Subgroup.centralPreimage (pCore 2 L)).Characteristic
  have hNC : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image L (centralCore L)
  have hPR : P ≤ normalizer (R : Set G) :=
    (P).le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hCQ : C ⊓ R ≤ C.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 P).to_le inf_le_right) inf_le_left
    exact (le_inf C.le_normalizer ((centralCore_le_point d).trans hPR)).trans
      inf_normalizer_le_normalizer_inf
  have hCL : C.pCoreIn 2 ≤ L.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _) (L.le_normalizer.trans hNC)
  have hc : ⁅R,C⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf ?_ ?_).trans (hCQ.trans hCL)
    · exact le_normalizer_iff_commutator_le_right.mp
        ((point_core_le_sylow (T:=T) (L:=L) (V₁:=V₁)).trans (d.normalizes_L.trans hNC))
    · exact le_normalizer_iff_commutator_le_left.mp ((centralCore_le_point d).trans hPR)
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  have hl : l ∈ centralCore L := hz
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer d.normalizes_L) x.property⟩ l
  have hm : l' * l⁻¹ ∈ pCore 2 L := by
    obtain ⟨a,ha,he⟩ := hc (commutator_mem_commutator hx (mem_map_of_mem L.subtype hl))
    exact (show a = l' * l⁻¹ from Subtype.ext he) ▸ ha
  rw [source_quotient_action_apply]
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul]
  exact (QuotientGroup.eq_one_iff (l' * l⁻¹)).mpr hm

private theorem covered_point_core_no_swap
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (x : X) (hx : x.val ∈ R) : ¬ (permutation s x).IsSwap := by
  obtain ⟨c⟩ := Section03.PointResidualImage.covered_flag_of_triple d hc
  let j := c.cover
  let := source_core_quotient_quasisimple s
  intro ht
  let t := permutation s x
  let a := source_quotient_action s x
  have hβ : MulAut.centralQuotientAction (source_central_quotient s) a =
      MulAut.conjNormal t := source_central_action s x
  have ht2 : t^2 = 1 := by rw [←ht.orderOf]; exact pow_orderOf_eq_one t
  have ha2 : a^2 = 1 := by
    apply MulAut.centralQuotientAction_injective (source_central_quotient s)
    rw [map_pow,map_one,hβ,←map_pow,ht2,map_one]
  have haout : ∀ b : L ⧸ pCore 2 L, a ≠ MulAut.conj b := by
    intro b hb
    let b' := source_central_quotient s (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) b)
    have hh : MulAut.conjNormal t = MulAut.conj b' := by
      rw [←hβ,hb,MulAut.centralQuotientAction_conj]
    have he : t = b'.val :=
      GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)
        (hh.trans (MulAut.conjNormal_val (h := b')).symm)
    have hs : Equiv.Perm.sign t = 1 := by
      rw [he]
      exact Equiv.Perm.mem_alternatingGroup.mp b'.property
    rw [ht.sign_eq] at hs
    norm_num at hs
  have hinv := Theory.HexEvenExtension.center_inverted_of_hex_model j a ha2 haout
  have hzcard : Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
    (Nat.card_congr (centerCongr j).toEquiv).trans Representation.Hexacode.even_center_card
  have hzbot : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hfix : a z = z := point_core_fixes_center d x hx z hz
    have hz2 : z^2 = 1 := by
      have he : z = z⁻¹ := hfix.symm.trans (hinv z hz)
      rw [pow_two]
      calc
        z * z = z⁻¹ * z := congrArg (fun w => w*z) he
        _ = 1 := inv_mul_cancel z
    have hz3 : z^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center (L ⧸ pCore 2 L)))
      rw [hzcard] at hh
      exact congrArg Subtype.val hh
    rw [pow_succ,hz2,one_mul] at hz3
    exact hz3
  rw [hzbot,card_bot] at hzcard
  contradiction
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
end
section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open ChapterC.NaturalSixControl
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
private theorem point_core_image_le (q : K →* Equiv.Perm (Fin 6))
    (hq : q.range = alternatingGroup (Fin 6) ∨ q.range = ⊤) :
    ((H1.comap q).pCoreIn 2).map q ≤ Model.E := by
  let P := H1.comap q
  let R := P.pCoreIn 2
  have hn : P ≤ normalizer (R : Set K) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hm : R.map q ≤ (P.map q).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 P).map q)
      (map_mono (pCoreIn_le 2 P)) ((map_mono hn).trans (R.le_normalizer_map q))
  have hP : P.map q = H1 ⊓ q.range := by
    change (H1.comap q).map q = _
    rw [map_comap_eq,inf_comm]
  rw [hP] at hm
  rw [←Model.pointCore_eq_exceptional]
  rcases hq with hq | hq
  · rw [hq] at hm
    change R.map q ≤ L1.pCoreIn 2 at hm
    rw [L1_core_eq_pointCoreEven] at hm
    exact hm.trans inf_le_left
  · rw [hq,inf_top_eq,H1_core_eq_pointCore] at hm
    exact hm

private theorem natural_point_thompson_centralizes
    (U R : Subgroup K) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (q : K →* Equiv.Perm (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hR : R.map q ≤ Model.E)
    (hs : ∀ x ∈ R, ¬ (q x).IsSwap) :
    elementaryAbelianMaxJ R ≤ centralizer (U : Set K) := by
  have hk : q.ker = centralizer (U : Set K) :=
    ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer U q e he
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (U : Set K) := q.ker_rangeRestrict.trans hk
  let ρ := NormalElementaryQuotient.representation U qr q.rangeRestrict_surjective hkr
  let a : Additive U ≃+ BinaryPermutation.natural (Fin 6) :=
    e.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let f : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    { a with map_smul' := ZMod.map_smul a }
  have hf (g : q.range) (v : Additive U) :
      f (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 6) g.val (f v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := NormalElementaryQuotient.representation_apply U qr
      q.rangeRestrict_surjective hkr g v
    have hh : (ρ (qr g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext hr
    change (e ((ρ (qr g) v).toMul)).toAdd = _
    rw [hh]
    exact he g v.toMul
  apply sSup_le
  intro A hA
  by_contra hn
  have hoff := NormalElementaryQuotient.maxElementary_isOffender U qr
    q.rangeRestrict_surjective hkr R A hUR hA (by rwa [hkr])
  have ht := hoff.map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 6))
    q.range.subtype q.range.subtype_injective f hf
  obtain ⟨B,hBA,hB⟩ := ht.exists_bestOffender _
  have hBA' : B ≤ A.map q := by
    rw [map_map] at hBA
    exact hBA
  have hb : ChapterB.Offenders.pairSwap 6 2 ∈ A.map q :=
    hBA' (Model.best_contains_swap (hBA'.trans ((map_mono hA.1).trans hR)) hB)
  obtain ⟨x,hx,heq⟩ := hb
  apply hs x (hA.1 hx)
  rw [heq]
  exact ⟨4,5,by decide,rfl⟩
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
end
section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion Section07 Section07.NaturalAction Section05.PlaneGeometry
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open BinaryPermutation
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T:Subgroup G) : Subgroup G)
local notation "P" => (one L (T:Subgroup G) V₁ ⊔ (T:Subgroup G) : Subgroup G)
local notation "R" => Subgroup.pCoreIn 2 P
local notation "Q" => Subgroup.pCoreIn 2 X
local notation "s" => localNaturalSetup d
include d

/-- The original covered equality J(O₂(L₁T)) = J(O₂(LT)), 13.2.2(8). -/
theorem covered_thompson_eq
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    ChapterB.thompsonJ R 0 = ChapterB.thompsonJ Q 0 := by
  let := local_module_normal s
  let := local_module_elementary s
  let := SourceCompletion.local_elementary d
  have hPX : P ≤ X := sup_le ((one_le L _ V₁).trans inf_le_left) le_sup_right
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hVT : V ≤ (T:Subgroup G) := (s).chosen.le_sylow
  have hVP : V ≤ P := hVT.trans le_sup_right
  have hVR : V ≤ R := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) hVP (hPX.trans d.normalizes_V)
  have hQP : Q ≤ P :=
    ((isPGroup_pCoreIn 2 X).le_sylow_of_normalized T
      (le_sup_right.trans ((X).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))).trans le_sup_right
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hQP
    (hPX.trans ((X).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hline : V₁ ≠ ⊥ := by
    intro he
    have hh := d.line_card
    rw [he,card_bot] at hh
    omega
  obtain ⟨v,hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hline
  have hvV : (v:G) ∈ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) v.property
  let w : V.subgroupOf X := ⟨⟨v,hVT.trans le_sup_right hvV⟩,hvV⟩
  let e := localCoordinate s
  let q := permutation s
  have hw : (e w).toAdd ≠ 0 := by
    intro he
    have hh : w = 1 := e.injective (he.trans (map_one e).symm)
    exact hv (Subtype.ext (congrArg (fun x : V.subgroupOf X => x.val.val) hh))
  obtain ⟨g,hg⟩ := NaturalTransport.transitive_nonzero (e w).toAdd (pairVector 4 5)
    hw pairVector45_ne_zero
  let q0 := (MulAut.conj g.val).toMonoidHom.comp q
  let e0 : V.subgroupOf X ≃* Multiplicative (natural (Fin 6)) :=
    e.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom g.val)).toAddEquiv.toMultiplicative
  have he0 : ∀ a u, (e0 (MulAut.conjNormal a u)).toAdd =
      naturalRepresentation (Fin 6) (q0 a) (e0 u).toAdd := by
    intro a u
    change naturalRepresentation (Fin 6) g.val (e (MulAut.conjNormal a u)).toAdd = _
    rw [localCoordinate_conjugation]
    change naturalRepresentation (Fin 6) g.val
      (naturalRepresentation (Fin 6) (q a) (e u).toAdd) =
      naturalRepresentation (Fin 6) (g.val * q a * g.val⁻¹)
        (naturalRepresentation (Fin 6) g.val (e u).toAdd)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have hw0 : (e0 w).toAdd = pairVector 4 5 := hg
  have hPc : (P).subgroupOf X = H1.comap q0 := by
    ext a
    have hfixed : a ∈ (P).subgroupOf X ↔ MulAut.conjNormal a w = w := by
      change a.val ∈ P ↔ _
      rw [point_product_eq d]
      change a.val ∈ X ∧ a.val ∈ normalizer (V₁:Set G) ↔ _
      rw [and_iff_right a.property]
      constructor
      · intro ha
        apply Subtype.ext
        apply Subtype.ext
        change a.val * v.val * a.val⁻¹ = v.val
        rw [←mem_centralizer_iff.mp (normalizer_le_centralizer_of_card_two V₁ d.line_card ha)
          v.val v.property,mul_inv_cancel_right]
      · intro ha
        have hgen : zpowers v.val = V₁ := by
          have hh := congrArg (Subgroup.map V₁.subtype)
            (zpowers_eq_top_of_prime_card d.line_card hv)
          simpa only [MonoidHom.map_zpowers,subtype_apply,←MonoidHom.range_eq_map,range_subtype] using hh
        apply Subgroup.centralizer_le_normalizer
        rw [←hgen,zpowers_eq_closure,centralizer_closure]
        apply mem_centralizer_singleton_iff.mpr
        exact mul_inv_eq_iff_eq_mul.mp
          (congrArg (fun x : V.subgroupOf X => x.val.val) ha)
    rw [hfixed]
    have hh : MulAut.conjNormal a w = w ↔
        naturalRepresentation (Fin 6) (q0 a) (pairVector 4 5) = pairVector 4 5 := by
      constructor
      · intro ha
        have he := he0 a w
        rw [ha,hw0] at he
        exact he.symm
      · intro ha
        apply e0.injective
        change (e0 (MulAut.conjNormal a w)).toAdd = (e0 w).toAdd
        rw [he0,hw0,ha]
    rw [hh,pairVector_map,pairVector_eq_iff ((q0 a).injective.ne (by decide)) (by decide)]
    change pair (q0 a 4) (q0 a 5) = pair 4 5 ↔ (pair 4 5).image (q0 a) = pair 4 5
    simp [pair]
  have hRc : (R).subgroupOf X = (H1.comap q0).pCoreIn 2 := by
    rw [←hPc,pCoreIn_subgroupOf 2 P X hPX]
  have hrange : q0.range = alternatingGroup (Fin 6) ∨ q0.range = ⊤ := by
    have hle : alternatingGroup (Fin 6) ≤ q0.range := by
      rw [←conjugate_alternating g.val]
      change (alternatingGroup (Fin 6)).map (MulAut.conj g.val).toMonoidHom ≤
        ((MulAut.conj g.val).toMonoidHom.comp q).range
      rw [MonoidHom.range_comp]
      exact map_mono (alternating_le_range s)
    have hi : q0.range.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · exact Or.inr (index_eq_one.mp hi)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi)
  have hJR : elementaryAbelianMaxJ ((R).subgroupOf X) ≤ centralizer (V.subgroupOf X : Set X) := by
    apply natural_point_thompson_centralizes (V.subgroupOf X) ((R).subgroupOf X)
      (subgroupOf_mono X hVR) q0 e0 he0
    · rw [hRc]
      exact point_core_image_le q0 hrange
    · intro x hx hs
      apply covered_point_core_no_swap d hc x hx
      obtain ⟨i,j,hij,hs⟩ := hs
      have hh : q x = g.val⁻¹ * Equiv.swap i j * g.val := by
        have he := congrArg (fun y => g.val⁻¹ * y * g.val) hs
        simpa only [q0,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
          mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he
      have hs : g.val⁻¹ * Equiv.swap i j * g.val =
          Equiv.swap (g.val⁻¹ i) (g.val⁻¹ j) := by
        simpa only [inv_inv] using (Equiv.swap_apply_apply g.val⁻¹ i j).symm
      exact ⟨_,_,g.val.symm.injective.ne hij,hh.trans hs⟩
  have hmap : (ChapterB.thompsonJ ((R).subgroupOf X) 0).map (X).subtype = ChapterB.thompsonJ R 0 := by
    rw [←ChapterB.thompsonJ_map_injective (X).subtype (X).subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  have hJC : ChapterB.thompsonJ R 0 ≤ centralizer (V:Set G) := by
    rw [←hmap,ChapterB.thompsonJ_zero]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (hJR hx ⟨y,hVT.trans le_sup_right hy⟩ hy)
  have hJQ : elementaryAbelianMaxJ R ≤ Q := by
    rw [←ChapterB.thompsonJ_zero,local_sylow_centralizer s (source_core_quotient_quasisimple s)]
    exact le_inf ((ChapterB.thompsonJ_le R 0).trans (point_core_le_sylow (T:=T) (L:=L) (V₁:=V₁))) hJC
  rw [ChapterB.thompsonJ_zero,ChapterB.thompsonJ_zero]
  exact (elementaryAbelianMaxJ_eq_of_intermediate R Q hJQ hQR).symm
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
end
section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
include d h

/-- The original covered L₁ normalizer bound, 13.2.2(9). -/
theorem covered_one_normalizer
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    normalizer (one L (T:Subgroup G) V₁ : Set G) ≤ M :=
  covered_one_normalizer_of_thompson d h hc (covered_thompson_eq d hc)

/-- Relative normality in an outside overgroup excludes the full covered L₁. -/
theorem outside_excludes_one
    (hc : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    {J Y : Subgroup G}
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (hn : (Y.subgroupOf J).Normal)
    (he : Y = one L (T:Subgroup G) V₁) : False := by
  have hh := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  rw [he] at hh
  exact hJ.2 (hh.trans (covered_one_normalizer d h hc))

/-- All original 13.3.9 clauses on the literal residual action. -/
theorem original_source :
    SolvableExclusion.Residual.Source1339 L (one L (T:Subgroup G) V₁)
      (plus L (T:Subgroup G) V₁) T M V V₁ :=
  source_of_covered_thompson d h (covered_thompson_eq d)

/-- Original 13.8.14 with 13.3.9 discharged. The independently proved
solvable-overgroup exclusion retains its original premise. -/
theorem original_whole_residual
    {H : Subgroup G} (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ (T:Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) :
    Components.Fitting.ResidualAlternatives H L (one L T V₁) (plus L T V₁) :=
  SourceCompletion.LocalFitting.whole_residual d hH (original_source d h) hex
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
end
