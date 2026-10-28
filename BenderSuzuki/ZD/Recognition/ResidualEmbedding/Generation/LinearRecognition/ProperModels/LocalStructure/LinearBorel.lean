module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Elementary
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.SE.InvolutionCore

/-!
# The actual PSL₂ Borel in a proper residual subgroup

For `L = residualGenerated M z t` with a genuine binary PSL₂ isomorphism,
local strong embedding supplies a Sylow two-subgroup of `L` in `M ∩ L`.
After Sylow conjugacy, the matrix root-generation theorem places this proper
intersection in the upper triangular Borel. Strong embedding then gives the
reverse inclusion. Thus the isomorphism identifies the actual local subgroup,
not just its isomorphism type.

Its involution core is the upper root group and has the field's order. This
identifies `A = ⟨Z ∩ M⟩` using `Elementary`, and identifies the two-core as a
Sylow subgroup. A second change of coordinates inside the Borel carries the
chosen involution `t` to the Weyl matrix. The literal subgroup `D ∩ L` is then
the diagonal torus. Matrix multiplication proves its inversion by `t`, its
cyclic order, and the genuine carrier product `M ∩ L = T (D ∩ L)`.
The same coordinates prove transitivity on the involutions outside `M`.

Source: GLS, Volume 4, Chapter 2, Lemma 12.2(b,d,f), and Chapter 4,
Lemma 3.2(b–e,i). These local conclusions need only product disconnection,
the supplied simple reduction, properness, and the actual model equivalence;
the elementary-core clause additionally uses the source containment `A ≤ L`.
-/

noncomputable section

open BenderSuzuki BenderSuzuki.Converse BenderSuzuki.PFAppendixIII Theory.GroupTheory
open Subgroup Matrix.SpecialLinearGroup BenderSuzuki.PFchapter1section1
open scoped Pointwise

private theorem stronglyEmbedded_equiv_Borel {F : Type*} [Field F] [Finite F] [CharP F 2]
    {H : Type*} [Group H] [Finite H] (M : Subgroup H)
    (hM : BenderSuzuki.IsStronglyEmbedded M) (e : H ≃* SL2 F) :
    ∃ f : H ≃* SL2 F, M.map f.toMonoidHom = Borel F := by
  let N := M.comap e.symm.toMonoidHom
  have hN : BenderSuzuki.IsStronglyEmbedded N := by
    apply hM.comap_of_injective e.symm.toMonoidHom e.symm.injective
    · intro htop
      apply hM.ne_top
      apply top_unique
      intro x _
      have hx : e x ∈ N := by change e x ∈ M.comap e.symm.toMonoidHom; rw [htop]; trivial
      simpa [N] using hx
    · obtain ⟨x, hx, hi⟩ := hM.exists_involution
      exact ⟨e x, by simpa [N] using hx,
        BenderSuzuki.IsInvolution.map_of_injective hi e.toMonoidHom e.injective⟩
  obtain ⟨S, hSN⟩ := hN.containsSylowTwo
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) S (upperUnipotentSylow F 2)
  let f := e.trans (MulAut.conj g)
  let P := M.map f.toMonoidHom
  have hUP : upperUnipotent F ≤ P := by
    have hle : (g • S : Sylow 2 (SL2 F)).toSubgroup ≤ N.map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono hSN
    rw [hg] at hle
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact ⟨e.symm y, hy, by simp [f]⟩
  have hP : P ≠ ⊤ := by
    intro htop
    apply hM.ne_top
    apply top_unique
    intro x _
    obtain ⟨y, hy, he⟩ := (show f x ∈ P from htop ▸ mem_top _)
    exact f.injective he ▸ hy
  have hPB : P ≤ Borel F := by
    intro x hx
    exact (mem_Borel_iff _).mpr ((mem_rankOneBorel_iff _).mp
      (overgroup_le_rankOneBorel hUP hP hx))
  refine ⟨f, le_antisymm hPB ?_⟩
  intro x hx
  have hu : uni (1 : F) ∈ upperUnipotent F := by
    apply (mem_upperUnipotent F _).mpr
    refine ⟨1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe]
  have hi : PFAppendixIII.IsInvolution (uni (1 : F)) := by
    refine ⟨?_, ?_⟩
    · intro he
      have hh := congrArg (fun a : SL2 F => a.val 0 1) he
      simp at hh
    · rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
  have hnorm : x ∈ normalizer (upperUnipotent F : Set (SL2 F)) :=
    (mem_rankOneBorel_iff _).mpr ((mem_Borel_iff _).mp hx)
  have hconj := (mem_normalizer_iff.mp hnorm (uni (1 : F))).mp hu
  have hM1 : f.symm (uni (1 : F)) ∈ M := by
    obtain ⟨y, hy, he⟩ := hUP hu
    simpa [← he] using hy
  have hMc : f.symm (x * uni (1 : F) * x⁻¹) ∈ M := by
    obtain ⟨y, hy, he⟩ := hUP hconj
    simpa [← he] using hy
  have hxM : f.symm x ∈ M := by
    apply hM.mem_of_involution_mem_rightConjugate hM1 ?_
      (BenderSuzuki.IsInvolution.map_of_injective hi f.symm.toMonoidHom f.symm.injective)
    rw [rightConjugate, Subgroup.conjBy, mem_map]
    refine ⟨f.symm (x * uni (1 : F) * x⁻¹), hMc, ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  exact ⟨f.symm x, hxM, f.apply_symm_apply x⟩

namespace BenderSuzuki.ZD
open PFchapter1section1

/-- The model isomorphism can be chosen to identify the actual local intersection
with the standard upper triangular subgroup. -/
public theorem residual_equiv_sl2_borel
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)) :
    ∃ e : residualGenerated M z t ≃* SL2 (BinaryGaloisField n),
      (M.comap (residualGenerated M z t).subtype).map e.toMonoidHom =
        Borel (BinaryGaloisField n) := by
  obtain ⟨e⟩ := hm
  let q : SL2 (BinaryGaloisField n) ≃* PSL2 (BinaryGaloisField n) :=
    MulEquiv.ofBijective (Converse.pi _) ⟨pi_injective, pi_surjective⟩
  exact stronglyEmbedded_equiv_Borel _
    (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL)
    (e.trans q.symm)

/-- The local intersection is the Borel as a group, with the subtype conventions
of the ambient source statement. -/
private noncomputable def localIntersectionBorelEquiv
    {G : Type*} [Group G] {M L : Subgroup G} {F : Type*} [Field F]
    (e : L ≃* SL2 F)
    (he : (M.comap L.subtype).map e.toMonoidHom = Borel F) :
    (M ⊓ L : Subgroup G) ≃* Borel F := by
  have h : (M ⊓ L).subgroupOf L = M.comap L.subtype := by
    ext x
    simp only [mem_subgroupOf, mem_inf, mem_comap, x.property, and_true]
    rfl
  exact (subgroupOfEquivOfLe (show M ⊓ L ≤ L from inf_le_right)).symm.trans
    ((MulEquiv.subgroupCongr h).trans
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr he)))
end BenderSuzuki.ZD

namespace BenderSuzuki.ZD.LinearBorel
variable {F : Type*} [Field F]

private theorem upperUnipotent_eq_Unip : upperUnipotent F = Unip F := by
  have h : upperUnipotentHom F = uniHom F := by
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotentHom, transvection_coe, uniHom]
  exact congrArg MonoidHom.range h

variable [CharP F 2]

private theorem unip_sq {x : SL2 F} (hx : x ∈ Unip F) : x ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := (mem_Unip_iff _).mp hx
  rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]

private theorem borel_sq_mem_unip {x : SL2 F} (hx : x ∈ Borel F) (h2 : x ^ 2 = 1) :
    x ∈ Unip F := by
  have h10 := (mem_Borel_iff _).mp hx
  have h00 : x.val 0 0 = 1 := by
    have hh := congrArg (fun a : SL2 F => a.val 0 0) h2
    have hs : x.val 0 0 ^ 2 = 1 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h10] using hh
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have h11 : x.val 1 1 = 1 := by rw [Borel_lower_right hx, h00, inv_one]
  apply (mem_Unip_iff _).mpr
  refine ⟨x.val 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem borel_involutionCore :
    involutionCore (Borel F) = (Unip F).subgroupOf (Borel F) := by
  rw [involutionCore_eq_closure]
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact borel_sq_mem_unip x.property (congrArg Subtype.val hx.sq_eq_one)
  · intro x hx
    by_cases h : x = 1
    · simpa only [h] using (closure (involutionsSet (Borel F))).one_mem
    · exact subset_closure ⟨h, Subtype.ext (unip_sq hx)⟩

private theorem borel_involutionCore_sq (x : involutionCore (Borel F)) : x ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact unip_sq (by simpa only [borel_involutionCore, mem_subgroupOf] using x.property)

private theorem card_borel_involutionCore : Nat.card (involutionCore (Borel F)) = Nat.card F := by
  rw [borel_involutionCore,
    Nat.card_congr (subgroupOfEquivOfLe (Unip_le_Borel (F := F))).toEquiv]
  exact (Nat.card_congr (MonoidHom.ofInjective (uniHom_injective (F := F))).toEquiv).symm

variable [Finite F]

private theorem borel_twoCore : pCore 2 (Borel F) = (Unip F).subgroupOf (Borel F) := by
  let S := (upperUnipotentSylow F 2).subtype
    (show upperUnipotent F ≤ Borel F by rw [upperUnipotent_eq_Unip]; exact Unip_le_Borel)
  have hS : (S : Subgroup (Borel F)) = (Unip F).subgroupOf (Borel F) := by
    change (upperUnipotent F).subgroupOf (Borel F) = _
    rw [upperUnipotent_eq_Unip]
  have hN : (S : Subgroup (Borel F)).Normal := by
    rw [hS, ← upperUnipotent_eq_Unip]
    apply normal_subgroupOf_of_le_normalizer
    intro x hx
    exact (mem_rankOneBorel_iff _).mpr ((mem_Borel_iff _).mp hx)
  rw [← hS]
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal S) (le_sSup ⟨hN, S.isPGroup'⟩)

private theorem borel_sylow_eq_twoCore :
    ∃ S : Sylow 2 (Borel F), (S : Subgroup (Borel F)) = pCore 2 (Borel F) := by
  refine ⟨(upperUnipotentSylow F 2).subtype
    (show upperUnipotent F ≤ Borel F by rw [upperUnipotent_eq_Unip]; exact Unip_le_Borel), ?_⟩
  rw [borel_twoCore]
  change (upperUnipotent F).subgroupOf (Borel F) = _
  rw [upperUnipotent_eq_Unip]
end BenderSuzuki.ZD.LinearBorel

namespace BenderSuzuki.ZD
open PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n))

include h r hz hzM ht htM hL hm

/-- The distinguished closure is the elementary abelian root group of order `2^n`. -/
public theorem psl2_distinguishedClosure_elementary_card
    (hn : 2 ≤ n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) ∧
      Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n := by
  obtain ⟨e, he⟩ := residual_equiv_sl2_borel h r hz hzM ht htM hL hm
  let B := M ⊓ residualGenerated M z t
  let f : B ≃* Borel (BinaryGaloisField n) := localIntersectionBorelEquiv e he
  let fI : involutionCore B ≃* involutionCore (Borel (BinaryGaloisField n)) :=
    (f.subgroupMap _).trans (MulEquiv.subgroupCongr (involutionCore_map_mulEquiv f))
  have hA := distinguishedClosure_eq_involutionCore_local h r hz hzM ht htM hL hAL
  let fA : involutionCore B ≃* closure (Z ∩ (M : Set G)) :=
    (equivMapOfInjective _ B.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hA)
  let a := fA.symm.trans fI
  have hsq (x : closure (Z ∩ (M : Set G))) : x ^ 2 = 1 := by
    apply a.injective
    rw [map_pow, map_one]
    exact LinearBorel.borel_involutionCore_sq _
  have hc : IsMulCommutative (closure (Z ∩ (M : Set G))) :=
    isMulCommutative_of_forall_sq_one hsq
  refine ⟨{ toIsMulCommutative := hc
            exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }, ?_⟩
  rw [Nat.card_congr a.toEquiv, LinearBorel.card_borel_involutionCore,
    card_binaryGaloisField n (by omega)]

/-- The two-core of the actual local intersection is Sylow in that intersection. -/
public theorem psl2_local_twoCore_sylow :
    ∃ S : Sylow 2 (M ⊓ residualGenerated M z t : Subgroup G),
      (S : Subgroup (M ⊓ residualGenerated M z t : Subgroup G)) =
        pCore 2 (M ⊓ residualGenerated M z t : Subgroup G) := by
  obtain ⟨e, he⟩ := residual_equiv_sl2_borel h r hz hzM ht htM hL hm
  let f := localIntersectionBorelEquiv e he
  obtain ⟨S, hS⟩ := LinearBorel.borel_sylow_eq_twoCore (F := BinaryGaloisField n)
  refine ⟨S.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective, ?_⟩
  change (S : Subgroup (Borel (BinaryGaloisField n))).map f.symm.toMonoidHom = _
  rw [hS, pCore_map_iso]
end BenderSuzuki.ZD

namespace BenderSuzuki.ZD.LinearBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem exists_borel_conj_weyl {x : SL2 F} (hx : PFAppendixIII.IsInvolution x)
    (hB : x ∉ Borel F) : ∃ b : Borel F, MulAut.conj (b : SL2 F) (weyl F) = x := by
  have hc : x.val 1 0 ≠ 0 := by simpa only [mem_Borel_iff] using hB
  have hdiag : x.val 1 1 = x.val 0 0 := by
    have hh := congrArg (fun a : SL2 F => a.val 1 0) hx.sq_eq_one
    have he : x.val 1 0 * (x.val 0 0 + x.val 1 1) = 0 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_comm] using hh
    have hh := (mul_eq_zero.mp he).resolve_left hc
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hh
  have hd : x.val 0 0 ^ 2 + x.val 0 1 * x.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hdiag, ← pow_two, sub_eq_add_neg, CharTwo.neg_eq]
      using x.property
  obtain ⟨d, hdc⟩ := isSquare_of_charTwo' (x.val 1 0)
  have hd0 : d ≠ 0 := by intro h; simp [h] at hdc; exact hc hdc
  let b : SL2 F := ⟨!![d⁻¹, x.val 0 0 / d; 0, d], by
    simp [Matrix.det_fin_two, hd0]⟩
  have hb : b ∈ Borel F := by rw [mem_Borel_iff]; rfl
  have hmul : b * weyl F = x * b := by
    apply Subtype.ext
    ext i j
    change (b.val * (weyl F).val) i j = (x.val * b.val) i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hdc, div_eq_mul_inv,
        mul_assoc, hd0, CharTwo.add_self_eq_zero]
    · field_simp
      rw [hdc] at hd
      linear_combination -hd
    · convert (CharTwo.add_self_eq_zero (x.val 0 0 * d)).symm using 1
      field_simp
  exact ⟨⟨b, hb⟩, by rw [MulAut.conj_apply, hmul, mul_assoc, mul_inv_cancel, mul_one]⟩
end BenderSuzuki.ZD.LinearBorel

namespace BenderSuzuki.ZD.LinearBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem borel_involution_conjugate {t v : SL2 F}
    (ht : PFAppendixIII.IsInvolution t) (htB : t ∉ Borel F)
    (hv : PFAppendixIII.IsInvolution v) (hvB : v ∉ Borel F) :
    ∃ b : Borel F, MulAut.conj (b : SL2 F) t = v := by
  obtain ⟨b, hb⟩ := exists_borel_conj_weyl ht htB
  obtain ⟨c, hc⟩ := exists_borel_conj_weyl hv hvB
  refine ⟨c * b⁻¹, ?_⟩
  rw [← hb, ← hc]
  simp [MulAut.conj_apply, mul_assoc]
end BenderSuzuki.ZD.LinearBorel

namespace BenderSuzuki.ZD
open PFchapter1section1

/-- The actual local intersection conjugates the chosen `t` to every outside involution in `L`. -/
public theorem psl2_local_involutions_conjugate
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n))
    {v : G} (hv : PFAppendixIII.IsInvolution v) (hvL : v ∈ residualGenerated M z t)
    (hvM : v ∉ M) : ∃ b ∈ M ⊓ residualGenerated M z t, MulAut.conj b t = v := by
  obtain ⟨e, he⟩ := residual_equiv_sl2_borel h r hz hzM ht htM hL hm
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left)
      (mem_zpowers t)
  let tL : residualGenerated M z t := ⟨t, htL⟩
  let vL : residualGenerated M z t := ⟨v, hvL⟩
  have hmem (x : residualGenerated M z t) : e x ∈ Borel (BinaryGaloisField n) ↔ (x : G) ∈ M := by
    rw [← he, mem_map_equiv, e.symm_apply_apply]
    exact Iff.rfl
  obtain ⟨b, hb⟩ := LinearBorel.borel_involution_conjugate
    (BenderSuzuki.IsInvolution.map_of_injective
      (BenderSuzuki.IsInvolution.subtype (h.involutions t ht) htL) e.toMonoidHom e.injective)
    (fun hx => htM ((hmem tL).mp hx))
    (BenderSuzuki.IsInvolution.map_of_injective
      (BenderSuzuki.IsInvolution.subtype hv hvL) e.toMonoidHom e.injective)
    (fun hx => hvM ((hmem vL).mp hx))
  let a := e.symm (b : SL2 (BinaryGaloisField n))
  have haM : (a : G) ∈ M := (hmem a).mp (by simp [a])
  refine ⟨a, ⟨haM, a.property⟩, ?_⟩
  have hh : MulAut.conj a tL = vL := by
    apply e.injective
    simpa [MulAut.conj_apply, a] using hb
  exact congrArg Subtype.val hh
end BenderSuzuki.ZD

namespace BenderSuzuki.ZD.LinearBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem borel_product : (Borel F : Set (SL2 F)) = (Unip F : Set (SL2 F)) * (Torus F : Set (SL2 F)) := by
  ext A
  constructor
  · intro hA
    have hne := Borel_diag_ne_zero hA
    have h11 := Borel_lower_right hA
    have h10 := (mem_Borel_iff _).mp hA
    refine ⟨uni (A.val 0 1 * A.val 0 0), (mem_Unip_iff _).mpr ⟨_, rfl⟩,
      tor (Units.mk0 (A.val 0 0) hne), ?_, ?_⟩
    · rw [Torus_eq_range]; exact ⟨_, rfl⟩
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, mul_assoc, mul_inv_cancel₀ hne]
  · rintro ⟨u, hu, d, hd, rfl⟩
    exact (Borel F).mul_mem (Unip_le_Borel hu) (Torus_le_Borel hd)

omit [Finite F] in
private theorem torus_eq_pair : Torus F = Borel F ⊓ rightConjugate (Borel F) (weyl F) := by
  rw [Borel, rightConjugate_stabilizer, weyl_inv, weyl_smul_pInf]
  rfl

private noncomputable def torusEquivUnits : Torus F ≃* Fˣ :=
  (MulEquiv.subgroupCongr (Torus_eq_range (F := F))).trans
    (MonoidHom.ofInjective (torHom_injective (F := F))).symm

omit [CharP F 2] in
private theorem torus_cyclic : IsCyclic (Torus F) :=
  isCyclic_of_injective ((torusEquivUnits (F := F)).toMonoidHom) (torusEquivUnits (F := F)).injective

omit [Finite F] [CharP F 2] in
private theorem torus_card : Nat.card (Torus F) = Nat.card F - 1 := by
  rw [Nat.card_congr torusEquivUnits.toEquiv, Nat.card_units]

omit [Finite F] in
private theorem torus_inverted {d : SL2 F} (hd : d ∈ Torus F) :
    rightConjugateElem d (weyl F) = d⁻¹ := by
  rw [Torus_eq_range] at hd
  obtain ⟨a, rfl⟩ := hd
  rw [rightConjugateElem, weyl_inv, ← map_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, torHom]
end BenderSuzuki.ZD.LinearBorel

namespace BenderSuzuki.ZD
open PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual local Borel and the chosen involution admit simultaneous matrix coordinates. -/
public theorem residual_equiv_sl2_borel_weyl
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)) :
    ∃ e : residualGenerated M z t ≃* SL2 (BinaryGaloisField n),
      (∀ x : residualGenerated M z t, e x ∈ Borel (BinaryGaloisField n) ↔ (x : G) ∈ M) ∧
      (∀ htL : t ∈ residualGenerated M z t, e ⟨t, htL⟩ = weyl (BinaryGaloisField n)) := by
  obtain ⟨f, hf⟩ := residual_equiv_sl2_borel h r hz hzM ht htM hL hm
  have hmem (x : residualGenerated M z t) : f x ∈ Borel (BinaryGaloisField n) ↔ (x : G) ∈ M := by
    rw [← hf, mem_map_equiv, f.symm_apply_apply]
    exact Iff.rfl
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left) (mem_zpowers t)
  obtain ⟨b, hb⟩ := LinearBorel.exists_borel_conj_weyl
    (BenderSuzuki.IsInvolution.map_of_injective
      (BenderSuzuki.IsInvolution.subtype (h.involutions t ht) htL) f.toMonoidHom f.injective)
    (fun hx => htM ((hmem ⟨t, htL⟩).mp hx))
  change MulAut.conj (b : SL2 (BinaryGaloisField n)) (weyl _) = f ⟨t, htL⟩ at hb
  let e := f.trans (MulAut.conj (b : SL2 (BinaryGaloisField n))⁻¹)
  refine ⟨e, ?_, ?_⟩
  · intro x
    change (b : SL2 (BinaryGaloisField n))⁻¹ * f x * (b : SL2 (BinaryGaloisField n))⁻¹⁻¹ ∈ _ ↔ _
    rw [inv_inv, ← hmem]
    exact (Borel (BinaryGaloisField n)).mul_mem_cancel_right b.property |>.trans
      ((Borel (BinaryGaloisField n)).mul_mem_cancel_left ((Borel _).inv_mem b.property))
  · intro htL'
    change (b : SL2 (BinaryGaloisField n))⁻¹ * f ⟨t, htL'⟩ * (b : SL2 (BinaryGaloisField n))⁻¹⁻¹ = _
    rw [← hb, MulAut.conj_apply]
    simp [mul_assoc]

end BenderSuzuki.ZD

namespace BenderSuzuki.ZD.LinearBorel
variable {G : Type*} [Group G] {M L : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem mem_rightConjugate_iff (M : Subgroup G) (t x : G) :
    x ∈ rightConjugate M t ↔ t * x * t⁻¹ ∈ M := by
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  simp [MulAut.conj_apply]

omit [Finite F] [CharP F 2] in
private theorem map_local_borel (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M) :
    (M.comap L.subtype).map e.toMonoidHom = Borel F := by
  ext x
  rw [mem_map_equiv]
  change (e.symm x : G) ∈ M ↔ x ∈ Borel F
  rw [← he, e.apply_symm_apply]

omit [Finite F] in
private theorem local_pair_mem (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M)
    {t : G} (htL : t ∈ L) (het : e ⟨t, htL⟩ = weyl F) (x : L) :
    e x ∈ Torus F ↔ (x : G) ∈ residualPairStabilizer M t := by
  rw [torus_eq_pair, mem_inf, mem_rightConjugate_iff,
    residualPairStabilizer, mem_inf, mem_rightConjugate_iff, he]
  have h := he (⟨t, htL⟩ * x * ⟨t, htL⟩⁻¹)
  simpa only [map_mul, map_inv, het, Subgroup.coe_mul, Subgroup.coe_inv] using and_congr_right (fun _ => h)

private theorem local_twoCore_mem (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M) (x : L) :
    (x : G) ∈ (pCore 2 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ↔ e x ∈ Unip F := by
  let f : (M ⊓ L : Subgroup G) ≃* Borel F :=
    BenderSuzuki.ZD.localIntersectionBorelEquiv e (map_local_borel e he)
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hf : f b ∈ (pCore 2 (M ⊓ L : Subgroup G)).map f.toMonoidHom := ⟨b, hb, rfl⟩
    rw [pCore_map_iso, borel_twoCore] at hf
    change e ⟨(b : G), b.property.2⟩ ∈ Unip F at hf
    convert hf using 1
    apply congrArg e
    exact Subtype.ext hbx.symm
  · intro hx
    have hxM := (he x).mp (Unip_le_Borel hx)
    let b : (M ⊓ L : Subgroup G) := ⟨x, hxM, x.property⟩
    have hf : f b ∈ pCore 2 (Borel F) := by
      rw [borel_twoCore]
      exact hx
    rw [← pCore_map_iso 2 f, mem_map_equiv] at hf
    exact ⟨b, by simpa using hf, rfl⟩

private noncomputable def localPairTorusEquiv (e : L ≃* SL2 F)
    (he : ∀ x : L, e x ∈ Borel F ↔ (x : G) ∈ M)
    {t : G} (htL : t ∈ L) (het : e ⟨t, htL⟩ = weyl F) :
    (residualPairStabilizer M t ⊓ L : Subgroup G) ≃* Torus F := by
  let E := residualPairStabilizer M t ⊓ L
  have hi : E.subgroupOf L = (residualPairStabilizer M t).comap L.subtype := by
    ext x
    simp only [E, mem_subgroupOf, mem_inf, mem_comap, x.property, and_true]
    rfl
  have hm : ((residualPairStabilizer M t).comap L.subtype).map e.toMonoidHom = Torus F := by
    ext x
    rw [mem_map_equiv]
    exact (local_pair_mem e he htL het (e.symm x)).symm.trans (by simp)
  exact (subgroupOfEquivOfLe (show E ≤ L from inf_le_right)).symm.trans
    ((MulEquiv.subgroupCongr hi).trans ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hm)))

end BenderSuzuki.ZD.LinearBorel

namespace BenderSuzuki.ZD
open PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal pair stabilizer in the residual subgroup is a cyclic torus. -/
public theorem psl2_local_pair_cyclic_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)) :
    IsCyclic (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) ∧
      Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) = 2 ^ n - 1 := by
  obtain ⟨e, he, het⟩ := residual_equiv_sl2_borel_weyl h r hz hzM ht htM hL hm
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left) (mem_zpowers t)
  let f := LinearBorel.localPairTorusEquiv e he htL (het htL)
  have := LinearBorel.torus_cyclic (F := BinaryGaloisField n)
  refine ⟨isCyclic_of_injective f.toMonoidHom f.injective, ?_⟩
  rw [Nat.card_congr f.toEquiv, LinearBorel.torus_card, card_binaryGaloisField n (by omega)]

/-- The source involution inverts every element of the literal local pair stabilizer. -/
public theorem psl2_local_pair_inverted
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n))
    {d : G} (hd : d ∈ residualPairStabilizer M t ⊓ residualGenerated M z t) :
    rightConjugateElem d t = d⁻¹ := by
  obtain ⟨e, he, het⟩ := residual_equiv_sl2_borel_weyl h r hz hzM ht htM hL hm
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left) (mem_zpowers t)
  let dL : residualGenerated M z t := ⟨d, hd.2⟩
  let tL : residualGenerated M z t := ⟨t, htL⟩
  have hi := LinearBorel.torus_inverted ((LinearBorel.local_pair_mem e he htL (het htL) dL).mpr hd.1)
  have hh : rightConjugateElem dL tL = dL⁻¹ := by
    apply e.injective
    change e (tL⁻¹ * dL * tL) = e (dL⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv, show e tL = weyl _ from het htL]
    exact hi
  exact congrArg Subtype.val hh

/-- The source Borel is the genuine carrier product of its two-core and local torus. -/
public theorem psl2_local_borel_product
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hm : Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)) :
    ((M ⊓ residualGenerated M z t : Subgroup G) : Set G) =
      (((pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
        (M ⊓ residualGenerated M z t).subtype) : Set G) *
      ((residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) : Set G) := by
  obtain ⟨e, he, het⟩ := residual_equiv_sl2_borel_weyl h r hz hzM ht htM hL hm
  have htL : t ∈ residualGenerated M z t :=
    (show zpowers t ≤ residualGenerated M z t from le_trans le_sup_right le_sup_left) (mem_zpowers t)
  ext x
  constructor
  · intro hx
    have hxB := (he ⟨x, hx.2⟩).mpr hx.1
    change e ⟨x, hx.2⟩ ∈ (Borel (BinaryGaloisField n) : Set _) at hxB
    rw [LinearBorel.borel_product] at hxB
    obtain ⟨u, hu, d, hd, hud⟩ := hxB
    let a := e.symm u
    let b := e.symm d
    have ha := (LinearBorel.local_twoCore_mem e he a).mpr (by simpa [a] using hu)
    have hb := (LinearBorel.local_pair_mem e he htL (het htL) b).mp (by simpa [b] using hd)
    refine ⟨a, ha, b, ⟨hb, b.property⟩, ?_⟩
    have hprod : a * b = ⟨x, hx.2⟩ := by
      apply e.injective
      simpa [a, b] using hud
    exact congrArg Subtype.val hprod
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', _, rfl⟩ := ha
    exact (M ⊓ residualGenerated M z t).mul_mem a'.property ⟨hb.1.1, hb.2⟩

end BenderSuzuki.ZD
