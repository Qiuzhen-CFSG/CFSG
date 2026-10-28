module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredNaturalPoint
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.Source
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.GroupTheory.NormalCentralQuotientAction.Maps

/-!
# Excluding the selected natural module above the cubic A₆ cover

A maximal elementary subgroup of the natural point radical that moves the
module would give a best offender containing a transposition. A lifted
transposition in the cubic cover inverts its center, whereas the point
radical fixes that center. Hence the point radical's Thompson subgroup
centralizes the natural module. The exact Sylow centralizer identifies it
with the Thompson subgroup of O₂(KT), and yields the Baumann equality.

Apply this to the same literal point radical identified in
ComponentCoveredNaturalPoint. Its Baumann normalizer lies in N_G(L), while
K normalizes that Baumann subgroup. This contradicts K's escape and excludes
the last covered natural branch of component recognition.

The final EscapingUniqueness consumer applies this exclusion at every
escaping point. Original earlier-source inputs retain their existing owners
and final discharge. No four-dimensional setup is imposed on the original
five-dimensional augmentation module.
Source: Aschbacher--Smith 13.2.2(8) and 13.4.10(3), printed pp.877--878,908.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CoveredNaturalThompson
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

open BinaryPermutation Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

theorem point_radical_thompson_centralizes
    (U : Subgroup K) [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* Equiv.Perm (Fin 6))
    (e : U ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd =
      naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (w : U) (hw : w ≠ 1)
    (hs : ∀ x ∈ (centralizer ({w.val} : Set K)).pCoreIn 2, ¬ (q x).IsSwap) :
    elementaryAbelianMaxJ ((centralizer ({w.val} : Set K)).pCoreIn 2) ≤
      centralizer (U : Set K) := by
  let C := centralizer ({w.val} : Set K)
  let R := C.pCoreIn 2
  have hw0 : (e w).toAdd ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  obtain ⟨g,hg⟩ := NaturalTransport.transitive_nonzero (e w).toAdd (pairVector 4 5)
    hw0 pairVector45_ne_zero
  let q0 := (MulAut.conj g.val).toMonoidHom.comp q
  let e0 : U ≃* Multiplicative (natural (Fin 6)) :=
    e.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom g.val)).toAddEquiv.toMultiplicative
  have he0 : ∀ a v, (e0 (MulAut.conjNormal a v)).toAdd =
      naturalRepresentation (Fin 6) (q0 a) (e0 v).toAdd := by
    intro a v
    change naturalRepresentation (Fin 6) g.val (e (MulAut.conjNormal a v)).toAdd = _
    rw [he]
    change naturalRepresentation (Fin 6) g.val
      (naturalRepresentation (Fin 6) (q a) (e v).toAdd) =
      naturalRepresentation (Fin 6) (g.val * q a * g.val⁻¹)
        (naturalRepresentation (Fin 6) g.val (e v).toAdd)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have hwe : (e0 w).toAdd = pairVector 4 5 := hg
  have hC : C = H1.comap q0 := by
    ext a
    have hf : a ∈ C ↔ MulAut.conjNormal a w = w := by
      rw [Subtype.ext_iff]
      change a ∈ centralizer ({w.val} : Set K) ↔ a * w.val * a⁻¹ = w.val
      rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul,eq_comm]
    rw [hf]
    have hh : MulAut.conjNormal a w = w ↔
        naturalRepresentation (Fin 6) (q0 a) (pairVector 4 5) = pairVector 4 5 := by
      constructor
      · intro ha
        have hh := he0 a w
        rw [ha,hwe] at hh
        exact hh.symm
      · intro ha
        apply e0.injective
        change (e0 (MulAut.conjNormal a w)).toAdd = (e0 w).toAdd
        rw [he0,hwe,ha]
    rw [hh,pairVector_map,pairVector_eq_iff ((q0 a).injective.ne (by decide)) (by decide)]
    change pair (q0 a 4) (q0 a 5) = pair 4 5 ↔ (pair 4 5).image (q0 a) = pair 4 5
    simp [pair]
  have hrange : q0.range = alternatingGroup (Fin 6) ∨ q0.range = ⊤ := by
    have hle : alternatingGroup (Fin 6) ≤ q0.range := by
      rw [←conjugate_alternating g.val]
      change (alternatingGroup (Fin 6)).map (MulAut.conj g.val).toMonoidHom ≤
        ((MulAut.conj g.val).toMonoidHom.comp q).range
      rw [MonoidHom.range_comp]
      exact map_mono hY
    have hi : q0.range.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · exact Or.inr (index_eq_one.mp hi)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi)
  have hUR : U ≤ R := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
    (by
      intro u hu
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) w))
    (le_top.trans U.normalizer_eq_top.ge)
  apply natural_point_thompson_centralizes U R hUR q0 e0 he0
  · change (C.pCoreIn 2).map q0 ≤ _
    rw [hC]
    exact point_core_image_le q0 hrange
  · intro x hx ht
    apply hs x hx
    obtain ⟨i,j,hij,ht⟩ := ht
    have hh : q x = g.val⁻¹ * Equiv.swap i j * g.val := by
      have hh := congrArg (fun y => g.val⁻¹ * y * g.val) ht
      simpa only [q0,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
        mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
    have ht : g.val⁻¹ * Equiv.swap i j * g.val =
        Equiv.swap (g.val⁻¹ i) (g.val⁻¹ j) := by
      simpa only [inv_inv] using (Equiv.swap_apply_apply g.val⁻¹ i j).symm
    exact ⟨_,_,g.val.symm.injective.ne hij,hh.trans ht⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CoveredNaturalThompson

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CoveredNaturalAction
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V)
variable (a : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
variable (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
variable (he : ∀ (l : L) (v : V),
  (e (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v)).toAdd =
    BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
      (a (QuotientGroup.mk' (centralCore L) l)) (e v).toAdd)

private def quotient :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) :=
  (centralPreimageQuotientEquiv (pCore 2 L)).symm.trans a

omit [Finite G] in
private theorem quotient_apply (l : L) :
    quotient a (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) =
      a (QuotientGroup.mk' (centralCore L) l) := by
  change a ((centralPreimageQuotientEquiv (pCore 2 L)).symm _) = _
  congr 1
  apply (Equiv.symm_apply_eq _).mpr
  exact (centralPreimageQuotientEquiv_mk (pCore 2 L) l).symm

omit [Finite G] in
private theorem centralAction
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion le_sup_left l) =
      (a (QuotientGroup.mk' (centralCore L) l)).val) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    MulAut.centralQuotientAction (quotient a) (augmentationQuotientAction D x) =
      MulAut.conjNormal (q x) := by
  apply MulEquiv.ext
  intro v
  obtain ⟨b,rfl⟩ := a.surjective v
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
  rw [← quotient_apply a l, MulAut.centralQuotientAction_apply,
    augmentationQuotientAction_apply, quotient_apply,
    quotient_apply]
  apply Subtype.ext
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩ l
  have he : inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l' =
      x * inclusion le_sup_left l * x⁻¹ := Subtype.ext rfl
  have hf := congrArg (q) he
  rw [map_mul, map_mul, map_inv, hqL, hqL] at hf
  exact hf


include D a e he
omit [Finite G] in
private theorem centralCore_le_point (z : V) :
    (centralCore L).map L.subtype ≤
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) := by
  refine le_inf ((map_subtype_le _).trans le_sup_left) ?_
  rintro _ ⟨l,hl,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := he l z
  have hlq : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  rw [hlq,map_one,map_one,Module.End.one_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp
    (congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))))

omit [Finite G] in
/-- The actual point radical fixes the center of the component's two-core quotient. -/
theorem point_core_fixes_center
    (v : V) (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : x.val ∈ ((L ⊔ (T : Subgroup G)) ⊓ centralizer ({v.val} : Set G)).pCoreIn 2)
    (z : L ⧸ pCore 2 L) (hz : z ∈ center (L ⧸ pCore 2 L)) :
    augmentationQuotientAction D x z = z := by
  let X := L ⊔ (T : Subgroup G)
  let P := X ⊓ centralizer ({v.val} : Set G)
  let R := P.pCoreIn 2
  let C := (centralCore L).map L.subtype
  let : (centralCore L).Characteristic :=
    inferInstanceAs (Subgroup.centralPreimage (pCore 2 L)).Characteristic
  have hNC : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image L (centralCore L)
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hCQ : C ⊓ R ≤ C.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 P).to_le inf_le_right) inf_le_left
    exact (le_inf C.le_normalizer ((centralCore_le_point D a e he v).trans hPR)).trans
      inf_normalizer_le_normalizer_inf
  have hCL : C.pCoreIn 2 ≤ L.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _) (L.le_normalizer.trans hNC)
  have hc : ⁅R,C⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf ?_ ?_).trans (hCQ.trans hCL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (((pCoreIn_le 2 P).trans inf_le_left).trans
          ((sup_le L.le_normalizer D.sylow_normalizes_component).trans hNC))
    · exact le_normalizer_iff_commutator_le_left.mp ((centralCore_le_point D a e he v).trans hPR)
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  have hl : l ∈ centralCore L := hz
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩ l
  have hm : l' * l⁻¹ ∈ pCore 2 L := by
    obtain ⟨a,ha,he⟩ := hc (commutator_mem_commutator hx (mem_map_of_mem L.subtype hl))
    exact (show a = l' * l⁻¹ from Subtype.ext he) ▸ ha
  rw [augmentationQuotientAction_apply]
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul]
  exact (QuotientGroup.eq_one_iff (l' * l⁻¹)).mpr hm

/-- A covered component's point radical has no transposition in its marked
natural action. -/
theorem point_core_no_swap
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion le_sup_left l) =
      (a (QuotientGroup.mk' (centralCore L) l)).val)
    (v : V) (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : x.val ∈ ((L ⊔ (T : Subgroup G)) ⊓ centralizer ({v.val} : Set G)).pCoreIn 2) :
    ¬ (q x).IsSwap := by
  obtain ⟨j⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode
    (quotient a) hc
  intro ht
  let aut := augmentationQuotientAction D x
  have hβ := centralAction D a q hqL x
  change MulAut.centralQuotientAction _ aut = _ at hβ
  have ht2 : (q x)^2 = 1 := by simpa only [ht.orderOf] using pow_orderOf_eq_one (q x)
  have ha2 : aut^2 = 1 := by
    apply MulAut.centralQuotientAction_injective (quotient a)
    rw [map_pow,map_one,hβ,←map_pow,ht2,map_one]
  have haout : ∀ b : L ⧸ pCore 2 L, aut ≠ MulAut.conj b := by
    intro b hb
    let b' := quotient a (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) b)
    have hh : MulAut.conjNormal (q x) = MulAut.conj b' := by
      rw [←hβ,hb,MulAut.centralQuotientAction_conj]
    have he : q x = b'.val :=
      GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)
        (hh.trans (MulAut.conjNormal_val (h := b')).symm)
    have hs : Equiv.Perm.sign (q x) = 1 := by
      rw [he]
      exact Equiv.Perm.mem_alternatingGroup.mp b'.property
    rw [ht.sign_eq] at hs
    norm_num at hs
  have hinv := Theory.HexEvenExtension.center_inverted_of_hex_model j aut ha2 haout
  have hzbot : center (L ⧸ pCore 2 L) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro z hz
    have hfix : aut z = z := point_core_fixes_center D a e he v x hx z hz
    have hz2 : z^2 = 1 := by
      have he : z = z⁻¹ := hfix.symm.trans (hinv z hz)
      rw [pow_two]
      calc
        z * z = z⁻¹ * z := congrArg (fun w => w*z) he
        _ = 1 := inv_mul_cancel z
    have hz3 : z^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center (L ⧸ pCore 2 L)))
      rw [hc] at hh
      exact congrArg Subtype.val hh
    rw [pow_succ,hz2,one_mul] at hz3
    exact hz3
  rw [hzbot,card_bot] at hc
  contradiction
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CoveredNaturalAction

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem covered_natural_point_thompson_baumann
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T K U)
    (a : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,D.normalizes k.property⟩ v)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (a (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (w : U) (hw : w ≠ 1) (hTw : (T : Subgroup G) ≤ centralizer ({w.val} : Set G)) :
    let R := ((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q ∧
      ChapterB.baumann R = ChapterB.baumann Q := by
  let X := K ⊔ (T : Subgroup G)
  let P := X ⊓ centralizer ({w.val} : Set G)
  let R := P.pCoreIn 2
  let Q := X.pCoreIn 2
  have hPX : P ≤ X := inf_le_left
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right hTw
  have hRX : R ≤ X := (pCoreIn_le 2 P).trans hPX
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T
      (hTP.trans (P.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
    (le_inf (pCoreIn_le 2 X)
      (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr w.property))))
    (hPX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hXU : X ≤ normalizer (U : Set G) := sup_le D.normalizes ((structural G T K h).2.2 U D).1
  have hXK : X ≤ normalizer (K : Set G) := sup_le K.le_normalizer D.sylow_normalizes_component
  let := D.elementary
  let lin : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    e.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let α := a.toMonoidHom.comp (QuotientGroup.mk' (centralCore K))
  obtain ⟨q,hqL,hqU,_⟩ := natural_extension X K U le_sup_left hXK hXU α
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) lin
      (fun k v => he k v.toMul)
  have hUX : U ≤ X := D.le_sylow.trans le_sup_right
  let W := U.subgroupOf X
  let : W.Normal := normal_subgroupOf_of_le_normalizer hXU
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUX
  let eu : W ≃* U := subgroupOfEquivOfLe hUX
  let eW := eu.trans e
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by
    simpa only [wi,eu.apply_symm_apply,map_one] using congrArg eu hh)
  have heW (x : X) (v : W) : (eW (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q x) (eW v).toAdd :=
    hqU x (Additive.ofMul (eu v))
  have hY : alternatingGroup (Fin 6) ≤ q.range := by
    intro b hb
    obtain ⟨c,hc⟩ := a.surjective ⟨b,hb⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (centralCore K) c
    exact ⟨inclusion le_sup_left k,(hqL k).trans (congrArg Subtype.val hc)⟩
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = P := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
  let := h.quasisimple
  have hJWC := CoveredNaturalThompson.point_radical_thompson_centralizes W q eW heW hY wi hwi
    (fun x hx => CoveredNaturalAction.point_core_no_swap D a e he hc q hqL w x (by
      change x.val ∈ R
      rw [←hRm]
      exact mem_map_of_mem X.subtype hx))
  have hJUC : elementaryAbelianMaxJ R ≤ centralizer (U : Set G) := by
    rw [←hRm,elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg Subtype.val (hJWC hx ⟨v,hUX hv⟩ hv)
  have hCQ : (T : Subgroup G) ⊓ centralizer (U : Set G) = Q :=
    RecognitionSource.chosen_sylow_centralizer_eq_core h D structural
  have hJQ : elementaryAbelianMaxJ R ≤ Q := by
    rw [←hCQ]
    exact le_inf ((sSup_le fun A hA => hA.1).trans hRT) hJUC
  have hJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q :=
    (elementaryAbelianMaxJ_eq_of_intermediate R Q hJQ hQR).symm
  refine ⟨hJ,?_⟩
  have hJQQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  have hUZ : U ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ Q) :=
    elementary_centralizer_maxJ_le_omegaCenter Q U D.le_core
      ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hJQQ))
  change R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set G) =
    Q ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  rw [hJ]
  apply le_antisymm
  · exact (le_inf (le_inf (inf_le_left.trans hRT)
      (inf_le_right.trans (centralizer_le hUZ)) |>.trans hCQ.le) inf_le_right)
  · exact inf_le_inf_right _ hQR
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The fixed-free natural covered row is impossible on the actual selected
component. Its common point radical has the same Baumann subgroup as O₂(KT),
so K normalizes a group whose normalizer lies in N_G(L). -/
theorem covered_natural_component_excluded
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (DK : ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G)),
      (e ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G).normalizerMonoidHom
        ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) :
    False := by
  obtain ⟨_,w,hw,hTw,_,hB⟩ := covered_natural_component_common_point
    h₀ h structural D m h1332 z hzT hzL hK hKN hKM hfK hc DK q e he
  have hqK := component_quotient_quasisimple h1332 hfK
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩ hqK
  have hb := (covered_natural_point_thompson_baumann hK12 structural DK q e he hc w hw hTw).2
  let X := K ⊔ (T : Subgroup G)
  have hKB : K ≤ normalizer (ChapterB.baumann
      (((K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G)).pCoreIn 2) : Set G) := by
    rw [hb]
    exact (le_sup_left.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))).trans
        (normalizer_le_normalizer_baumann (X.pCoreIn 2))
  exact hKM (hKB.trans hB)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
