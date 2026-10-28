module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicInvolutions
public import Theory.GroupTheory.CentralCoverCenteredModules
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.Defs
public import Theory.GroupTheory.SylowKernelCore

/-!
# The original hexad two-core and its cubic-central factor

For a finite group of type J4, retain the original cubic quotient and its
Sylow three-subgroup X. The literal preimage of a native hexad stabilizer
is the source G₁,₃. Its two-core intersected with C_H(X) is elementary of
order 32, contains Z(H), and maps onto the native translation kernel.

The central-cover calculation gives the order and elementary structure.
Frattini's product H = Q N_H(X) then identifies the two-core of the
intersection with the intersection of the two-core, preserving the actual
quotient maps and relative normalizers.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6), p.598, DOI 10.1007/BF01232280.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry LocalGeometry.LocalSubgroups

theorem native_hexad_twoCore {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    pCore 2 (MulAction.stabilizer M22 B) = (m22SetAction B).ker := by
  let K := (m22SetAction B).ker
  let q := (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    (QuotientGroup.mk' K)
  have hq : Function.Surjective q :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp
      (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (m22HexadQuotientAlternatingEquiv hB).injective, QuotientGroup.ker_mk']
  let : IsElementaryAbelian 2 K := m22HexadKernel_elementaryAbelian hB
  have hK : K ≤ pCore 2 (MulAction.stabilizer M22 B) :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 K⟩
  apply le_antisymm _ hK
  have hp : IsPGroup 2 ((pCore 2 (MulAction.stabilizer M22 B)).map q) :=
    pCore_isPGroup.map q
  let : ((pCore 2 (MulAction.stabilizer M22 B)).map q).Normal :=
    Normal.map inferInstance q hq
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hm : (pCore 2 (MulAction.stabilizer M22 B)).map q = ⊥ := by
    rcases (inferInstance : ((pCore 2 (MulAction.stabilizer M22 B)).map q).Normal).eq_bot_or_eq_top
      with he | he
    · exact he
    · have htwo := hp.of_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)
      obtain ⟨n, hn⟩ := htwo.exists_card_eq
      have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        norm_num
      have hd : 3 ∣ 2 ^ n := by rw [← hn, hc]; norm_num
      have hh := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd
      norm_num at hh
  rw [← hk]
  exact (Subgroup.map_eq_bot_iff _).mp hm

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

def originalHexad (B : Finset (Fin 22)) : Subgroup (fullCubicCentralizer e X) :=
  (MulAction.stabilizer M22 B).comap (fullCubicSimpleProjection h e X)

def originalHexadProjection (B : Finset (Fin 22)) :
    originalHexad h e X B →* MulAction.stabilizer M22 B :=
  (fullCubicSimpleProjection h e X).subgroupComap (MulAction.stabilizer M22 B)

theorem originalHexadProjection_surjective (B : Finset (Fin 22)) :
    Function.Surjective (originalHexadProjection h e X B) :=
  (fullCubicSimpleProjection h e X).subgroupComap_surjective_of_surjective _
    (fullCubicSimpleProjection_surjective h e X)

theorem originalHexadProjection_kernel_central (B : Finset (Fin 22)) :
    (originalHexadProjection h e X B).ker ≤ center (originalHexad h e X B) := by
  intro a ha
  have hak : (a : fullCubicCentralizer e X) ∈ (fullCubicSimpleProjection h e X).ker :=
    congrArg Subtype.val ha
  rw [fullCubicSimpleProjection_ker] at hak
  exact mem_center_iff.mpr fun b => Subtype.ext (mem_center_iff.mp hak b)

theorem originalHexad_twoCore_image {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (pCore 2 (originalHexad h e X B)).map (originalHexadProjection h e X B) =
      (m22SetAction B).ker := by
  rw [(originalHexadProjection h e X B).map_pCore_of_central_kernel_centered
    (originalHexadProjection_surjective h e X B)
    (originalHexadProjection_kernel_central h e X B), native_hexad_twoCore hB]

theorem originalHexad_twoCore_elementary {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (pCore 2 (originalHexad h e X B)) := by
  let P := (pCore 2 (originalHexad h e X B)).map (originalHexad h e X B).subtype
  have hP : IsPGroup 2 P := pCore_isPGroup.map _
  have hthree : IsPGroup 3 (fullCubicScalar e X) :=
    IsPGroup.of_card (n := 1) (by rw [fullCubicScalar_card h e X]; norm_num)
  have hdis := hP.disjoint_of_coprime hthree (by decide)
  have hs (a : pCore 2 (originalHexad h e X B)) : a ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have ham : originalHexadProjection h e X B a.val ∈ (m22SetAction B).ker :=
      (originalHexad_twoCore_image h e X hB).le (mem_map_of_mem _ a.property)
    let : IsElementaryAbelian 2 (m22SetAction B).ker := m22HexadKernel_elementaryAbelian hB
    have haq : fullCubicSimpleProjection h e X a.val.val ^ 2 = 1 :=
      congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian _ ham)
    exact disjoint_def.mp hdis
      (P.pow_mem (mem_map_of_mem _ a.property) 2)
      (fullCubic_square_mem_scalar h e X a.val.val haq)
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

theorem originalHexad_twoCore_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (pCore 2 (originalHexad h e X B)) = 32 := by
  let I := originalHexad h e X B
  let P := pCore 2 I
  let f := fullCubicSimpleProjection h e X
  let g := (originalHexadProjection h e X B).comp P.subtype
  let C := (fullCubicProjection h e X).ker
  have hCf : C ≤ f.ker := by
    intro x hx
    change (innerProjection e) ((cubicCentralizerProjection h e X)
      (fullCubicProjection h e X x)) = 1
    rw [show fullCubicProjection h e X x = 1 from hx, map_one, map_one]
  have hCI : C ≤ I := fun x hx => by
    change f x ∈ MulAction.stabilizer M22 B
    rw [show f x = 1 from hCf hx]
    exact one_mem _
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 1)
    (by rw [fullCubicProjection_kernel_card h e X]; norm_num)
  have hCP : C.subgroupOf I ≤ P := le_sSup ⟨inferInstance, hC.comap_subtype⟩
  let j : C →* g.ker := {
    toFun x := ⟨⟨⟨x.val, hCI x.property⟩, hCP x.property⟩, Subtype.ext (hCf x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := fun x y he =>
    Subtype.ext (congrArg (fun a : g.ker => a.val.val.val) he)
  have hlow : 2 ∣ Nat.card g.ker := by
    have hh := Subgroup.card_dvd_of_injective j hj
    rwa [fullCubicProjection_kernel_card h e X] at hh
  let k : g.ker →* f.ker := {
    toFun a := ⟨a.val.val.val, congrArg Subtype.val a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hk : Function.Injective k := by
    intro a b he
    have he' : a.val.val.val = b.val.val.val :=
      congrArg (fun x : f.ker => x.val) he
    exact Subtype.ext (Subtype.ext (Subtype.ext he'))
  have hdiv : Nat.card g.ker ∣ 6 := by
    have hh := Subgroup.card_dvd_of_injective k hk
    rwa [fullCubicSimpleProjection_ker, fullCubicCentralizer_center_card h e X] at hh
  have hn3 : ¬ 3 ∣ Nat.card g.ker := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup.to_subgroup g.ker).exists_card_eq
    intro hd
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd)
  have hcard : Nat.card g.ker = 2 := by
    have hh : Nat.card g.ker ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    rw [show Nat.divisors 6 = {1, 2, 3, 6} from by decide +kernel] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h3 | h6
    · rw [h1] at hlow
      exact ((by decide : ¬ 2 ∣ 1) hlow).elim
    · exact h2
    · exact (hn3 (by rw [h3])).elim
    · exact (hn3 (by rw [h6]; norm_num)).elim
  have hr : g.range = (m22SetAction B).ker := by
    rw [← originalHexad_twoCore_image h e X hB]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hh := g.ker.card_mul_index
  rw [hcard, index_ker, hr, m22HexadKernel_card hB] at hh
  exact hh.symm

theorem originalHexad_marker_le (B : Finset (Fin 22)) :
    (fullCubicProjection h e X).ker ≤
      (pCore 2 (originalHexad h e X B)).map (originalHexad h e X B).subtype := by
  let C := (fullCubicProjection h e X).ker
  let I := originalHexad h e X B
  have hCI : C ≤ I := by
    intro a ha
    change fullCubicSimpleProjection h e X a ∈ MulAction.stabilizer M22 B
    have hh : fullCubicSimpleProjection h e X a = 1 := by
      change (innerProjection e) ((cubicCentralizerProjection h e X)
        (fullCubicProjection h e X a)) = 1
      rw [show fullCubicProjection h e X a = 1 from ha, map_one, map_one]
    rw [hh]
    exact one_mem _
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 1)
    (by rw [fullCubicProjection_kernel_card h e X]; norm_num)
  have hCP : C.subgroupOf I ≤ pCore 2 I := le_sSup ⟨inferInstance, hC.comap_subtype⟩
  intro a ha
  exact ⟨⟨a, hCI ha⟩, hCP ha, rfl⟩

def originalHexadCore (B : Finset (Fin 22)) : Subgroup (centralizer z) :=
  ((pCore 2 (originalHexad h e X B)).map (originalHexad h e X B).subtype).map
    (fullCubicCentralizer e X).subtype

/-- The original cubic-central hexad core is elementary of order 32 and
contains the original central involution. No cocode marking is assumed. -/
theorem originalHexadCore_data {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadCore h e X B) ∧
    Nat.card (originalHexadCore h e X B) = 32 ∧
    center (centralizer z) ≤ originalHexadCore h e X B := by
  have hE := originalHexad_twoCore_elementary h e X hB
  let := hE
  have hE' : IsElementaryAbelian 2
      ((pCore 2 (originalHexad h e X B)).map (originalHexad h e X B).subtype) :=
    IsElementaryAbelian.map_subtype
  let := hE'
  refine ⟨IsElementaryAbelian.map_subtype, ?_, ?_⟩
  · rw [originalHexadCore, card_map_of_injective (fullCubicCentralizer e X).subtype_injective,
      card_map_of_injective (originalHexad h e X B).subtype_injective,
      originalHexad_twoCore_card h e X hB]
  · have hh := map_mono (f := (fullCubicCentralizer e X).subtype)
      (originalHexad_marker_le h e X B)
    have hc : center (centralizer z) ≤ fullCubicCentralizer e X := center_le_centralizer _
    rw [fullCubicProjection_ker, map_subgroupOf_eq_of_le hc] at hh
    exact hh

theorem inner_mem_designStabilizer (B : Finset (Fin 22)) (a : M22) :
    MulAut.conj a ∈ designStabilizer B ↔ a ∈ MulAction.stabilizer M22 B := by
  constructor
  · rintro ⟨b, hb, he⟩
    have he' : M22ValueBound.Concrete.designAutEquiv b =
        M22ValueBound.Concrete.designAutEquiv (M22ValueBound.Concrete.inclusion a) :=
      he.trans (M22ValueBound.Concrete.designAutEquiv_inclusion a).symm
    have hb' := M22ValueBound.Concrete.designAutEquiv.injective he'
    rw [hb'] at hb
    exact hb
  · intro ha
    exact ⟨M22ValueBound.Concrete.inclusion a, ha,
      M22ValueBound.Concrete.designAutEquiv_inclusion a⟩

/-- The source plane-hexad subgroup under the unchanged full cubic quotient. -/
def originalPlaneHexad (B : Finset (Fin 22)) : Subgroup (centralizer z) :=
  (designStabilizer B).comap (CubicLift.projection e)

/-- The earlier cubic-central preimage is the literal intersection with
the source plane-hexad subgroup. -/
theorem originalHexad_eq_subgroupOf (B : Finset (Fin 22)) :
    originalHexad h e X B =
      (originalPlaneHexad e B).subgroupOf (fullCubicCentralizer e X) := by
  ext a
  change fullCubicSimpleProjection h e X a ∈ MulAction.stabilizer M22 B ↔
    CubicLift.projection e a.val ∈ designStabilizer B
  change fullCubicSimpleProjection h e X a ∈ MulAction.stabilizer M22 B ↔
    e.projection (QuotientGroup.mk' (core z) a.val) ∈ designStabilizer B
  rw [← fullCubicSimpleProjection_conj h e X a]
  exact (inner_mem_designStabilizer B _).symm

theorem originalHexadCore_eq (B : Finset (Fin 22)) :
    originalHexadCore h e X B =
      (originalPlaneHexad e B ⊓ fullCubicCentralizer e X : Subgroup (centralizer z)).pCoreIn 2 := by
  change ((originalHexad h e X B).pCoreIn 2).map (fullCubicCentralizer e X).subtype = _
  rw [map_pCoreIn_of_injective 2 _ _ (fullCubicCentralizer e X).subtype_injective,
    originalHexad_eq_subgroupOf h e X B, subgroupOf_map_subtype]

/-- The actual source hexad/cubic normalizer preserves the same elementary
order-32 subgroup, including its marker line. No inverter is selected. -/
theorem originalHexadCore_normalized (B : Finset (Fin 22)) :
    originalPlaneHexad e B ⊓ normalizer (cubicSylowImage e X : Set (centralizer z)) ≤
      normalizer (originalHexadCore h e X B : Set (centralizer z)) := by
  rw [originalHexadCore_eq h e X B]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (originalPlaneHexad e B ⊓ fullCubicCentralizer e X) (pCore 2 _))
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf (inf_le_left.trans (originalPlaneHexad e B).le_normalizer)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer (cubicSylowImage e X)))

include h in
/-- Frattini's original cubic product transfers the centralizer two-core
to the two-core of every subgroup containing the original Q. -/
theorem original_cubicCentralizer_twoCore
    (H : Subgroup (centralizer z)) (hQH : core z ≤ H) :
    (H ⊓ fullCubicCentralizer e X).pCoreIn 2 =
      H.pCoreIn 2 ⊓ fullCubicCentralizer e X := by
  let C := fullCubicCentralizer e X
  let P := (H ⊓ C).pCoreIn 2
  have hPH : P ≤ H := (pCoreIn_le 2 (H ⊓ C)).trans inf_le_left
  have hPC : P ≤ C := (pCoreIn_le 2 (H ⊓ C)).trans inf_le_right
  have hPN : H ⊓ normalizer (cubicSylowImage e X : Set (centralizer z)) ≤
      normalizer (P : Set (centralizer z)) := by
    apply le_trans _ (normalizer_le_normalizer_characteristic_image
      (H ⊓ C) (pCore 2 (H ⊓ C : Subgroup (centralizer z))))
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (inf_le_left.trans H.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer (cubicSylowImage e X)))
  have hQP : IsPGroup 2 (core z ⊔ P : Subgroup (centralizer z)) :=
    (IsPGroup.of_card h.core_card).to_sup_of_normal_left (isPGroup_pCoreIn 2 (H ⊓ C))
  have hHN : H ≤ normalizer ((core z ⊔ P : Subgroup (centralizer z)) : Set (centralizer z)) := by
    intro g hg
    obtain ⟨q,n,he⟩ := exists_core_mul_cubicNormalizer e h X g
    have hnH : n.val ∈ H := by
      have hh := H.mul_mem (H.inv_mem (hQH q.property)) hg
      rw [← he] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hn : n.val ∈ normalizer ((core z ⊔ P : Subgroup (centralizer z)) : Set (centralizer z)) :=
      normalizer_inf_normalizer_le_normalizer_sup (core z) P
        ⟨le_normalizer_of_normal (show n.val ∈ (⊤ : Subgroup (centralizer z)) from mem_top _),
          hPN ⟨hnH,n.property⟩⟩
    rw [← he]
    exact (normalizer ((core z ⊔ P : Subgroup (centralizer z)) : Set (centralizer z))).mul_mem
      ((core z ⊔ P : Subgroup (centralizer z)).le_normalizer
        ((le_sup_left : core z ≤ core z ⊔ P) q.property)) hn
  have hPcore : P ≤ H.pCoreIn 2 :=
    le_sup_right.trans (le_pCoreIn_of_normalizes hQP (sup_le hQH hPH) hHN)
  apply le_antisymm (le_inf hPcore hPC)
  apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le inf_le_left)
    (inf_le_inf (pCoreIn_le 2 H) le_rfl)
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf
    (inf_le_left.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
    (inf_le_right.trans C.le_normalizer)

/-- The same rank-five subgroup is exactly the source's
O₂(hexad preimage) intersect C_H(X). -/
theorem originalHexadCore_eq_source (B : Finset (Fin 22)) :
    originalHexadCore h e X B =
      (originalPlaneHexad e B).pCoreIn 2 ⊓ fullCubicCentralizer e X := by
  rw [originalHexadCore_eq h e X B]
  apply original_cubicCentralizer_twoCore h e X
  intro x hx
  change e.projection (QuotientGroup.mk' (core z) x) ∈ designStabilizer B
  have hq : QuotientGroup.mk' (core z) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [hq, map_one]
  exact one_mem _

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
