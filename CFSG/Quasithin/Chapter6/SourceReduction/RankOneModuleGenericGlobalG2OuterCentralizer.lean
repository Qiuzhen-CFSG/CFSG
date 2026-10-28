module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterInvolution
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Transfer
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterRootModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# The original outer involution's centralizer extension factor

The Hall torus is uniquely determined by its marking through the same whole
amalgam overlap. Thus the torus in the checked outer-involution construction
is the torus in the checked splitting T = S N_T(D), rather than a separately
chosen Hall subgroup. Its cyclic complement U centralizes each of its elements.
Consequently C_T(t) = C_S(t) U and |C_T(t)| = |C_S(t)| [T:S].
The complement order divides the original field degree n and is less than q.
The actual right-quotient field involution has a fixed field of order sqrt(q).

These are exact statements about the original subgroups and the same outer
involution; in particular they do not identify C_T(t) as an ambient Sylow
subgroup. The actual six-root conjugation identity gives |C_S(t)| ≤ q³, hence
|C_T(t)| < q⁴, by transport through the original right map. Proving that
root-action identity and the ambient Sylow placement of F.4.37 remain
necessary for the F.4.38 contradiction.
The Chapter 12 companion retains the literal quotient and whole-overlap maps.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, printed pp.289,293–294,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem split_card {S U T : Subgroup G}
    (hST : S ≤ T) (hUT : U ≤ T) (hd : Disjoint S U)
    (hs : (T : Set G) = (S : Set G) * (U : Set G)) :
    Nat.card T = Nat.card S * Nat.card U := by
  let f : S × U → T := fun x => ⟨x.1.val*x.2.val,T.mul_mem (hST x.1.property) (hUT x.2.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact mul_injective_of_disjoint hd (congrArg Subtype.val he)
    · intro x
      have hx : x.val ∈ (S : Set G) * (U : Set G) := hs ▸ x.property
      obtain ⟨s,hs,u,hu,he⟩ := hx
      exact ⟨(⟨s,hs⟩,⟨u,hu⟩),Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_prod S U)

private theorem split_index {S U T : Subgroup G}
    (hST : S ≤ T) (hUT : U ≤ T) (hd : Disjoint S U)
    (hs : (T : Set G) = (S : Set G) * (U : Set G)) :
    Nat.card U = S.relIndex T := by
  have hc : Nat.card S * S.relIndex T = Nat.card T := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ S T bot_le hST
  rw [split_card hST hUT hd hs] at hc
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

omit [Finite G] in
private theorem centralizer_split {S U T : Subgroup G}
    (hST : S ≤ T) (hUT : U ≤ T)
    (hs : (T : Set G) = (S : Set G) * (U : Set G))
    (t : G) (hU : U ≤ centralizer ({t} : Set G)) :
    ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) =
      ((S ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) * (U : Set G) := by
  ext x
  constructor
  · rintro ⟨hxT,hxC⟩
    have hx : x ∈ (S : Set G) * (U : Set G) := hs ▸ hxT
    obtain ⟨s,hs,u,hu,rfl⟩ := hx
    refine ⟨s,⟨hs,?_⟩,u,hu,rfl⟩
    change s ∈ centralizer ({t} : Set G)
    have hh := (centralizer ({t} : Set G)).mul_mem hxC
      ((centralizer ({t} : Set G)).inv_mem (hU hu))
    simpa only [mul_inv_cancel_right] using hh
  · rintro ⟨s,⟨hs,hsc⟩,u,hu,rfl⟩
    exact ⟨T.mul_mem (hST hs) (hUT hu),(centralizer ({t} : Set G)).mul_mem hsc (hU hu)⟩

omit [Finite G] in
private theorem cyclic_centralizer {U : Subgroup G} (hc : IsCyclic U)
    (t : G) (ht : t ∈ U) : U ≤ centralizer ({t} : Set G) := by
  let := hc
  intro u hu
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Commute.all (⟨u,hu⟩ : U) ⟨t,ht⟩).eq)

private theorem split_centralizer_card {S U T : Subgroup G}
    (hST : S ≤ T) (hUT : U ≤ T) (hd : Disjoint S U)
    (hs : (T : Set G) = (S : Set G) * (U : Set G))
    (hc : IsCyclic U) (t : G) (ht : t ∈ U) :
    Nat.card (T ⊓ centralizer ({t} : Set G) : Subgroup G) =
      Nat.card (S ⊓ centralizer ({t} : Set G) : Subgroup G) * S.relIndex T := by
  have hU := cyclic_centralizer hc t ht
  rw [split_card (inf_le_inf_right _ hST) (le_inf hUT hU)
    (hd.mono_left inf_le_left) (centralizer_split hST hUT hs t hU),
    split_index hST hUT hd hs]

private theorem marked_torus_unique
    {T : Sylow 2 G} {L W H A B D E : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmarkD : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ Atlas.G2.splitTorus)
    (hmarkE : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ E ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) : D=E := by
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  apply le_antisymm
  · intro x hx
    exact (hmarkE ⟨x,hC (hD hx)⟩).mpr ((hmarkD ⟨x,hC (hD hx)⟩).mp hx)
  · intro x hx
    exact (hmarkD ⟨x,hC (hE hx)⟩).mpr ((hmarkE ⟨x,hC (hE hx)⟩).mp hx)

/-- The same marked torus gives the exact centralizer decomposition for every
one of its original Sylow normalizers. Its extension factor has order [T:S],
dividing the original field degree and strictly smaller than the field order. -/
theorem Preparation.g2_outer_torus_centralizer
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ Atlas.G2.splitTorus)
    (t : T) (ht : t.val ∈ normalizer (D : Set G)) :
    let U := (T : Subgroup G) ⊓ normalizer (D : Set G)
    U ≤ centralizer ({t.val} : Set G) ∧
      ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Set G) =
        ((sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) : Set G) * (U : Set G) ∧
      Nat.card U = (sourceS L H).relIndex (T : Subgroup G) ∧
      Nat.card U ∣ n ∧ Nat.card U < Nat.card F ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
        Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
          (sourceS L H).relIndex (T : Subgroup G) := by
  obtain ⟨E,hE,_,hmarkE,hd,hcyc,hs⟩ := d.g2_source_sylow_torus_split h hTH hp F e
  have hDE : D=E := marked_torus_unique d h hTH F e hD hE hmark hmarkE
  subst E
  have hST := sourceS_le_sylow h.sylow_normalizes hTH
  have hd' := hd.mono_right (show (T : Subgroup G) ⊓ normalizer (D : Set G) ≤
    normalizer (D : Set G) from inf_le_right)
  have hi := split_index hST inf_le_left hd' hs
  have hc := cyclic_centralizer hcyc t.val ⟨t.property,ht⟩
  have hn := d.g2_source_sylow_index_dvd h hTH hp F (Or.inr ⟨e⟩)
  refine ⟨hc,centralizer_split hST inf_le_left hs t.val hc,hi,hi ▸ hn,?_,
    split_centralizer_card hST inf_le_left hd' hs hcyc t.val ⟨t.property,ht⟩⟩
  rw [hi,(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
  exact (Nat.le_of_dvd (by have := h.exponent; omega : 0<n) hn).trans_lt Nat.lt_two_pow_self

/-- The actual outer involution retains its quotient field coefficient and
marked Hall torus. Its fixed field has square-root order, and its centralizer
in T has the exact extension factor [T:S], at most n. -/
theorem Preparation.g2_exists_outer_involution_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ C ∧ IsHallSubgroup oddPrimes (D.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H ∧
        t.val ∈ normalizer (D : Set G) ∧ orderOf (residualSylowFieldAction hTH eR t)=2 ∧
        Nat.card (FixedBy.subfield F (residualSylowFieldAction hTH eR t))^2=Nat.card F ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
          Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
            (sourceS L H).relIndex (T : Subgroup G) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤
          Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) * n := by
  obtain ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ⟩ :=
    d.g2_exists_outer_involution h hTH hp F e hne
  have hc := d.g2_outer_torus_centralizer h hTH hp F e hD hmark t htD
  have hσ2 := (orderOf_eq_prime_iff.mp hσ).1
  have hσne := (orderOf_eq_prime_iff.mp hσ).2
  have hfixed : Nat.card (FixedBy.subfield F (residualSylowFieldAction hTH eR t))^2 =
      Nat.card F := FiniteField.card_involution_fixed_sq _ (fun x => by
        have he := congrArg (fun σ : F ≃+* F => σ x) hσ2
        exact he) hσne
  refine ⟨D,hD,hHall,hmark,eR,t,ht,htS,htD,hσ,hfixed,hc.2.2.2.2.2,?_⟩
  rw [hc.2.2.2.2.2]
  apply Nat.mul_le_mul_left
  rw [←hc.2.2.1]
  exact Nat.le_of_dvd (by have := h.exponent; omega : 0<n) hc.2.2.2.1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]

/-- The actual six-root conjugation identity gives the q³ fixed-point bound
and hence the strict q⁴ upper bound for C_T(t). Root preservation, encoded by
the displayed identity, and the ambient Sylow placement are still required. -/
theorem Preparation.g2_outer_involution_centralizer_lt_of_root_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ sourceS L H)
    (htD : t.val ∈ normalizer (D : Set G))
    (ρ : Fin 6 → F ≃+ F)
    (hroot : ∀ v : Fin 6 → F,
      t.val * (e.right.symm ⟨unipotentProduct v,
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩).val * t.val⁻¹ =
      (e.right.symm ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩).val) :
    Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hUS := source_g2_inverse_sylow_image d h hH.1.1.2 e
  have hUP : unipotent (K := F) ≤ parabolic₁ := le_sup_left.trans borel_le_parabolic₁
  let eU : unipotent (K := F) ≃* sourceS L H :=
    ((subgroupOfEquivOfLe hUP).symm.trans
      (equivMapOfInjective (unipotent.subgroupOf parabolic₁) f hf)).trans
        (MulEquiv.subgroupCongr hUS)
  let τ : normalizer (sourceS L H : Set G) :=
    ⟨t.val,sylow_normalizes_sourceS h.sylow_normalizes hH.1.1.2 t.property⟩
  let cS := (sourceS L H).normalizerMonoidHom τ
  let a : MulAut (unipotent (K := F)) := MulAut.congr eU.symm cS
  have he (x : unipotent (K := F)) : eU (a x)=cS (eU x) := eU.apply_symm_apply _
  have hact (v : Fin 6 → F) : a (unipotentEquiv v) =
      unipotentEquiv (fun i => ρ i (v i)) := by
    apply eU.injective
    rw [he]
    apply Subtype.ext
    exact hroot v
  have hτ : τ^2=1 := Subtype.ext
    (congrArg (fun x : T => x.val) (orderOf_eq_prime_iff.mp ht2).1)
  have hcS : cS^2=1 := by
    change ((sourceS L H).normalizerMonoidHom τ)^2=1
    rw [←map_pow,hτ,map_one]
  have ha2 : a^2=1 := by
    change (MulAut.congr eU.symm cS)^2=1
    rw [←map_pow,hcS,map_one]
  have hane : a≠1 := by
    intro ha1
    have hc1 : cS=1 := (MulAut.congr eU.symm).injective (ha1.trans (map_one _).symm)
    have hK := d.g2_right_maximal_all h hH hp F (Or.inr ⟨e⟩)
    have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hK.1
    have hzQ : center (residual H) ≤ pCore 2 (residual H) :=
      (center_le_centralizer (pCore 2 (residual H) : Set (residual H))).trans hchar
    have hsyl := d.sylow 1
    change ∃ R : Sylow 2 (residual H),
      (R : Subgroup (residual H)).map (residual H).subtype = sourceS L H ⊓ residual H at hsyl
    obtain ⟨R,hR⟩ := hsyl
    have hQS : (residual H).pCoreIn 2 ≤ sourceS L H := by
      have hh := pCoreIn_le_sylow (residual H) R
      rw [hR] at hh
      exact hh.trans inf_le_left
    have hzS := (map_mono hzQ).trans hQS
    have htC : t.val ∈ centralizer
        (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) := by
      apply mem_centralizer_iff.mpr
      intro z hz
      have hh := congrArg (fun b : MulAut (sourceS L H) => (b ⟨z,hzS hz⟩).val) hc1
      change t.val*z*t.val⁻¹=z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact htS (d.g2_center_fixer_le_sourceS h hH.1.1.2 hp F (Or.inr ⟨e⟩) ⟨t.property,htC⟩)
  have hfixed := G2OuterRootModel.fixed_card_le_cube a ρ
    (fun v => congrArg Subtype.val (hact v)) ha2 hane
  let j : (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) → a.fixedSubgroup :=
    fun x => ⟨eU.symm ⟨x.val,x.property.1⟩, (MulAut.mem_fixedSubgroup _ _).mpr (by
      apply eU.injective
      rw [he,eU.apply_symm_apply]
      apply Subtype.ext
      change t.val*x.val*t.val⁻¹=x.val
      rw [←mem_centralizer_singleton_iff.mp x.property.2,mul_inv_cancel_right])⟩
  have hj : Function.Injective j := by
    intro x y heq
    apply Subtype.ext
    exact congrArg (fun z : sourceS L H => z.val)
      (eU.symm.injective (congrArg Subtype.val heq))
  have hbound := (Nat.card_le_card_of_injective j hj).trans hfixed
  refine ⟨hbound,?_⟩
  have hc := d.g2_outer_torus_centralizer h hH.1.1.2 hp F e hD hmark t htD
  have hi : (sourceS L H).relIndex (T : Subgroup G) < Nat.card F := by
    rw [←hc.2.2.1]
    exact hc.2.2.2.2.1
  calc
    Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
      Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
        (sourceS L H).relIndex (T : Subgroup G) := hc.2.2.2.2.2
    _ ≤ Nat.card F^3 * (sourceS L H).relIndex (T : Subgroup G) := Nat.mul_le_mul_right _ hbound
    _ < Nat.card F^3 * Nat.card F := Nat.mul_lt_mul_of_pos_left hi (pow_pos Nat.card_pos _)
    _ = Nat.card F^4 := (pow_succ _ 3).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
