module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure

/-!
# Common fixed letters for elementary subgroups of HS

An elementary subgroup of order greater than eight in the actual degree-100
HS carrier has a common fixed letter if each of its elements fixes some letter.
Conjugate into the marked Sylow two-subgroup. Of its 512 elements, only 48
can square to one and fix a letter; twelve of these move letter zero. For
each of those twelve, a checked eight-color certificate bounds any commuting
subset of the eligible centralizer by eight. Thus the subgroup fixes zero.

The finite certificates use the two separating letters of the existing
Sylow enumeration. The remaining counting and Sylow transport are structural.
The generator in `ElementaryFixedPoint/source/generate.py` reproduces the
packed data and certificates from the retained ATLAS permutation tables.
All certificates are checked by the Lean kernel.

Source: the ATLAS HSG1-p100B0 action and its attribution retained in
`EvenLocalCandidates/source/README.md`; GLS volume 3, Table 5.3m, p.274.
This model calculation supports the HS case of the nonsingular-centralizer
argument in Aschbacher--Smith 12.6.12 (printed pp.825--826).
-/

namespace Sporadic.LeechRelated.HS.LiftedElementaryPoint
open EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 10000

-- BEGIN GENERATED CERTIFICATES
private def goodRow (i0 : Fin 48) : Fin 512 :=
  ⟨(10938327434375500616383596098733991892080480955071224683255607549991585425314375298627421682219359966383353040091168766768888414720 >>> (9 * (i0.val))) % 512 % 512, Nat.mod_lt _ (by decide)⟩

private def goodCode (i0 : Fin 512) : Fin 48 :=
  ⟨(970073734345035735721978690644662904108006966375364300687890605343010410553406475148034522559069579556863682438306617997263186931143335854816433404290658896416799440174713601284906520569130051164613170648746267806666904022333955200126434063292756396781267586453491284300199296361958419666999521799117114628104432713571116385851971182690992031681032242046403773271964667841527922349065762568896724257939644009981110048887770202373023128713550922291060132141432680114651446043837718320415787770078098230739490220818187003956646648069573660032669589096904872346814016510512786268576707062525725880221193503440735119590524440820770873253896589105994286608085737191011563599126292959470855299148023667007901600520578135366057958308448410121109769430517987896620773129727389368527306688573151697363857391113897020718661420818549106469907269355155917590058305254329327917004324357086242336755530965744282900638663188544 >>> (6 * (i0.val))) % 64 % 48, Nat.mod_lt _ (by decide)⟩

private def badRow (i0 : Fin 12) : Fin 48 :=
  ⟨(3072094594887821582657 >>> (6 * (i0.val))) % 64 % 48, Nat.mod_lt _ (by decide)⟩

private def badCode (i0 : Fin 48) : Fin 12 :=
  ⟨(272661399217417708148272323513228559628664528961536 >>> (4 * (i0.val))) % 16 % 12, Nat.mod_lt _ (by decide)⟩

private def centralRow (i0 : Fin 12) (i1 : Fin 16) : Fin 48 :=
  ⟨(43678632990180536423896583637789331845228561010147762365341726603544041134338746897898047200095805914489361921832862518718605063384249001190465133616594196375492144910502245406963643919976094926281109629944595600880232793784274142358988198030508020431365687413442324292506501703315521530582616403351725955518609989136160683523397483783570370867264 >>> (6 * (16 * i0.val + i1.val))) % 64 % 48, Nat.mod_lt _ (by decide)⟩

private def centralCode (i0 : Fin 12) (i1 : Fin 48) : Fin 16 :=
  ⟨(14503390936408882166722851687611914980393467569927275815542291041082573402111208426234897279997459384522528324789566049084704791750021983012659034585492714349569347379732103895125763502794176358943393157446248582760069607284902392058884497499679488697378187354589898316365322777719590558879166116455307425598922650729949339033009443897633892115994284993484665693540323414673824116121287082740430257876043660202690786115160539093167490674159754801631585408890633602397883128642107482275031458628795239703141457459972271148287202888557797022659871341889359725708187193670749040699693947038999300242390804010424201801612679016291701554040497983800494290238434365101552455986091656878562063949840 >>> (4 * (48 * i0.val + i1.val))) % 16 % 16, Nat.mod_lt _ (by decide)⟩

private def color (i0 : Fin 12) (i1 : Fin 16) : Fin 8 :=
  ⟨(245319695541187292565293123832133690363473133054747631398675436015869541412837144017090969947888080255793389416962947320624636057998930342593609985786348742326379447921821320 >>> (3 * (16 * i0.val + i1.val))) % 8 % 8, Nat.mod_lt _ (by decide)⟩

private def commutes (i j : Fin 48) : Prop :=
  point (goodRow i) (point (goodRow j) 1) = point (goodRow j) (point (goodRow i) 1) ∧
  point (goodRow i) (point (goodRow j) 4) = point (goodRow j) (point (goodRow i) 4)
private instance (i j : Fin 48) : Decidable (commutes i j) := inferInstanceAs (Decidable (_ ∧ _))

private theorem good_coverage : ∀ i : Fin 512,
    point i (point i 1) = 1 → point i (point i 4) = 4 →
      (∃ p : Fin 100, point i p = p) → goodRow (goodCode i) = i := by
  apply allFin
  decide +kernel

private theorem bad_coverage : ∀ i : Fin 48,
    point (goodRow i) 0 ≠ 0 → badRow (badCode i) = i := by
  apply allFin
  decide +kernel

private theorem central_coverage : ∀ i : Fin 12, ∀ j : Fin 48,
    commutes (badRow i) j → centralRow i (centralCode i j) = j := by
  apply allFin₂
  decide +kernel

private theorem color_separation : ∀ i : Fin 12, ∀ j k : Fin 16,
    color i j = color i k → commutes (centralRow i j) (centralRow i k) → j = k := by
  apply allFin
  decide +kernel
-- END GENERATED CERTIFICATES

open Subgroup Theory.GroupTheory EvenLocalCandidates
open scoped IsMulCommutative

/-- An elementary subgroup of order greater than eight in the marked Sylow,
all of whose elements fix some letter, fixes letter zero pointwise. -/
public theorem sylow_common_fixed_point (E : Subgroup subgroup) [IsElementaryAbelian 2 E]
    (hcard : 8 < Nat.card E)
    (hfix : ∀ x : E, ∃ p : Fin 100, (x.val.val : Equiv.Perm (Fin 100)) p = p) :
    ∀ x : E, (x.val.val : Equiv.Perm (Fin 100)) 0 = 0 := by
  let row (x : E) : Fin 512 := enumeration.symm x.val
  have row_spec (x : E) : element (row x) = x.val.val :=
    congrArg Subtype.val (enumeration.apply_symm_apply x.val)
  have square_point (x : E) (p : Fin 100) : point (row x) (point (row x) p) = p := by
    have hs : x.val.val ^ 2 = 1 :=
      congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
    rw [←row_spec x] at hs
    have hh := congrArg (fun z : Carrier => (z : Equiv.Perm (Fin 100)) p) hs
    simpa only [pow_two,Subgroup.coe_mul,Equiv.Perm.coe_mul,Function.comp_apply,
      element_point,Subgroup.coe_one,Equiv.Perm.one_apply] using hh
  have cover (x : E) : goodRow (goodCode (row x)) = row x := by
    apply good_coverage _ (square_point x 1) (square_point x 4)
    obtain ⟨p,hp⟩ := hfix x
    refine ⟨p,?_⟩
    rw [←element_point,row_spec]
    exact hp
  have hc (x y : E) : commutes (goodCode (row x)) (goodCode (row y)) := by
    have hp (p : Fin 100) : point (row x) (point (row y) p) =
        point (row y) (point (row x) p) := by
      have hh : x.val.val * y.val.val = y.val.val * x.val.val :=
        congrArg (fun z : E => z.val.val) (mul_comm x y)
      rw [←row_spec x,←row_spec y] at hh
      simpa only [Subgroup.coe_mul,Equiv.Perm.coe_mul,Function.comp_apply,element_point]
        using congrArg (fun z : Carrier => (z : Equiv.Perm (Fin 100)) p) hh
    exact ⟨by simpa only [cover] using hp 1,by simpa only [cover] using hp 4⟩
  intro x
  by_contra hx
  have hbad : badRow (badCode (goodCode (row x))) = goodCode (row x) := by
    apply bad_coverage
    rw [cover,←element_point,row_spec]
    exact hx
  let i := badCode (goodCode (row x))
  have hcentral (y : E) : centralRow i (centralCode i (goodCode (row y))) =
      goodCode (row y) := by
    apply central_coverage
    rw [show badRow i = goodCode (row x) from hbad]
    exact hc x y
  let f (y : E) : Fin 8 := color i (centralCode i (goodCode (row y)))
  have hf : Function.Injective f := by
    intro y z he
    have hh := color_separation i (centralCode i (goodCode (row y)))
      (centralCode i (goodCode (row z))) he (by rw [hcentral,hcentral]; exact hc y z)
    have hg : goodCode (row y) = goodCode (row z) := by
      rw [←hcentral y,←hcentral z,hh]
    have hr : row y = row z := by
      simpa only [cover] using congrArg goodRow hg
    exact Subtype.ext (enumeration.symm.injective hr)
  have hb : Nat.card E ≤ 8 := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  omega


/-- Every elementary subgroup of the actual HS carrier of order greater than
eight, with no fixed-point-free element, has a common fixed letter. -/
public theorem common_fixed_point (W : Subgroup Carrier) [IsElementaryAbelian 2 W]
    (hcard : 8 < Nat.card W)
    (hfix : ∀ w ∈ W, ∃ p : Fin 100, (w : Equiv.Perm (Fin 100)) p = p) :
    ∃ p : Fin 100, ∀ w ∈ W, (w : Equiv.Perm (Fin 100)) p = p := by
  obtain ⟨P,hWP⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier P BlockNormalizer.baseSylow
  let c := MulAut.conj g
  have hP : (P : Subgroup Carrier).map c.toMonoidHom = subgroup :=
    congrArg Sylow.toSubgroup hg
  let W' := W.map c.toMonoidHom
  have hW : W' ≤ subgroup := hP ▸ map_mono hWP
  let E := W'.subgroupOf subgroup
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map c.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hW
  have hc : 8 < Nat.card E := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hW).toEquiv,card_map_of_injective c.injective]
    exact hcard
  have hf : ∀ x : E, ∃ p : Fin 100, (x.val.val : Equiv.Perm (Fin 100)) p = p := by
    intro x
    obtain ⟨w,hw,he⟩ := x.property
    obtain ⟨p,hp⟩ := hfix w hw
    refine ⟨(g : Equiv.Perm (Fin 100)) p,?_⟩
    have he' : c w = x.val.val := he
    rw [←he']
    change ((g : Equiv.Perm (Fin 100)) * (w : Equiv.Perm (Fin 100)) *
      (g : Equiv.Perm (Fin 100))⁻¹) ((g : Equiv.Perm (Fin 100)) p) = _
    simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply,hp]
  refine ⟨(g : Equiv.Perm (Fin 100))⁻¹ 0,?_⟩
  intro w hw
  let y : E := ⟨⟨c w,hW (mem_map_of_mem c.toMonoidHom hw)⟩,mem_map_of_mem c.toMonoidHom hw⟩
  have hh := sylow_common_fixed_point E hc hf y
  change ((g : Equiv.Perm (Fin 100)) * (w : Equiv.Perm (Fin 100)) *
    (g : Equiv.Perm (Fin 100))⁻¹) 0 = 0 at hh
  have he := congrArg (fun p => (g : Equiv.Perm (Fin 100))⁻¹ p) hh
  simpa only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using he

end Sporadic.LeechRelated.HS.LiftedElementaryPoint
