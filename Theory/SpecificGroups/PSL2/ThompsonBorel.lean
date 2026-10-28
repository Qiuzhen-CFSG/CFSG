module
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry
public import Theory.GroupTheory.MaxElementaryImageComparison
public import Theory.GroupTheory.GeneralizedFitting.ElementarySylowThompsonNormalizer

/-!
# Thompson normalization for binary linear component Borels

For degree n > 2, an elementary automorphism group with an outer actor has
order at most 2^(n/2+1), strictly below the component Sylow order 2^n.
Maximum-elementary replacement therefore makes J of a component-normalizing
two-subgroup act inner, and also puts the full component Sylow inside J.
The inner-action normalizer calculation gives Borel normalization of J.

The component-pair replacement theorem then removes the normalization
hypothesis: J(S) cannot exchange the components. Thompson heredity gives the
same Borel normalization for the original S. All bounds concern the actual
conjugation image; the final transport retains the caller's finite field.
Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098, with the
binary PSL₂ automorphism bounds of GLS2, Theorem 26.24.
-/

public section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace Theory.PSL2.OrdinaryBorel

/-- An elementary subgroup with an outer actor is strictly smaller than the
component Sylow except at the source's exceptional field of four elements. -/
theorem outer_elementary_card_lt {n : ℕ} (hn : 2<n)
    (D : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 D]
    (hout : ¬ D ≤ inner (BinaryField n)) : Nat.card D < 2^n := by
  obtain ⟨a,haD,haouter⟩ := SetLike.not_le_iff_exists.mp hout
  let f := (fieldProjection (BinaryField n)).comp D.subtype
  let j : f.ker →* MulAut (BinaryGroup n) := D.subtype.comp f.ker.subtype
  have hj : Function.Injective j := Subtype.coe_injective.comp Subtype.coe_injective
  have hjinner (x : f.ker) : j x ∈ inner (BinaryField n) := by
    rw [←fieldProjection_ker]
    exact x.property
  have hjcomm (x : f.ker) : Commute (j x) a :=
    congrArg Subtype.val (mul_comm (x:D) ⟨a,haD⟩)
  have hker : Nat.card f.ker ≤ 2^(n/2) :=
    twoGroup_inner_centralizing_outer_card_le (by omega) (binary_semilinear_coverage (by omega))
      ((IsElementaryAbelian.isPGroup 2 D).to_subgroup f.ker) j hj hjinner a
      (elemPow_eq_one_of_isElementaryAbelian a haD) haouter hjcomm
  let : IsCyclic (BinaryField n ≃+* BinaryField n) := OuterSolvable.finiteFieldAut_isCyclic
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : Nat.card f.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0<2)
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 f.range
  calc
    Nat.card D = Nat.card f.ker * Nat.card f.range := by
      rw [←index_ker,f.ker.card_mul_index]
    _ ≤ 2^(n/2)*2 := Nat.mul_le_mul hker hr
    _ = 2^(n/2+1) := (pow_succ _ _).symm
    _ < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)

variable {G : Type*} [_root_.Group G] [Finite G]

/-- For degree greater than two, J(Q) acts inner and contains the component Sylow. -/
theorem normalizing_thompson (L Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQL : Q ≤ normalizer (L : Set G)) (P : Sylow 2 L)
    (hPQ : (P : Subgroup L).map L.subtype ≤ Q)
    {n : ℕ} (hn : 2<n) (e : L ≃* BinaryGroup n) :
    (normalizer (P : Set L)).map L.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ Q : Set G) := by
  let f : Q →* MulAut (BinaryGroup n) := (MulAut.congr e).toMonoidHom.comp
    (L.normalizerMonoidHom.comp (inclusion hQL))
  let U := (P : Subgroup L).map L.subtype
  let W := U.subgroupOf Q
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eP : P ≃* R := e.subgroupMap (P : Subgroup L)
  let : IsElementaryAbelian 2 R := sylow_elementary R
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hPQ
  have hcardP : Nat.card P=2^n := (Nat.card_congr eP.toEquiv).trans
    ((sylow_card R).trans (GaloisField.card 2 n (by omega)))
  have hcardW : Nat.card W=2^n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPQ).toEquiv,
      card_map_of_injective L.subtype_injective,hcardP]
  have hfon (l : L) (hl : (l:G) ∈ Q) : f ⟨l,hl⟩=MulAut.conj (e l) := by
    ext y
    change e (L.normalizerMonoidHom ⟨l,hQL hl⟩ (e.symm y))=e l*y*(e l)⁻¹
    change e (l*(e.symm y)*l⁻¹)=_
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
  have hker (x : Q) : x ∈ f.ker ↔ (x:G) ∈ centralizer (L:Set G) := by
    change MulAut.congr e (L.normalizerMonoidHom ⟨x,hQL x.property⟩)=1 ↔ _
    rw [←(MulAut.congr e).map_one,(MulAut.congr e).injective.eq_iff]
    change (⟨x,hQL x.property⟩:normalizer (L:Set G)) ∈ L.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hWker : Disjoint W f.ker := by
    apply disjoint_def.mpr
    intro w hw hk
    obtain ⟨l,hl,he⟩ := hw
    have hwe : (⟨l,hPQ (mem_map_of_mem L.subtype hl)⟩:Q)=w := Subtype.ext he
    have hh : MulAut.conj (e l)=1 := (hfon l _).symm.trans (hwe ▸ hk)
    have heone : e l=1 := psl2_conj_eq_one_implies (e l) hh
    have hlone : l=1 := e.injective (heone.trans e.map_one.symm)
    apply Subtype.ext
    exact he.symm.trans (congrArg (fun l : L => (l:G)) hlone)
  have hWC (A : Subgroup Q) : W ≤ centralizer (A⊓f.ker : Set Q) := by
    intro w hw a ha
    obtain ⟨l,hl,he⟩ := hw
    have hh := (hker a).mp ha.2
    apply Subtype.ext
    change (a:G)*(w:G)=(w:G)*(a:G)
    have he' : (l:G)=(w:G) := he
    rw [←he']
    exact (hh l l.property).symm
  have himageW : Nat.card (W.map f)=2^n := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map W f
    rw [hWker.eq_bot,card_bot,one_mul,hcardW] at hh
    exact hh
  have hinnerA (A : Subgroup Q) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤:Subgroup Q)) :
      A.map f ≤ inner (BinaryField n) := by
    let : IsElementaryAbelian 2 A := hA.2.1
    let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    by_contra hout
    have hh := Stellmacher.maxElementary_image_card_ge ⊤ A W f hA le_top (hWC A)
    rw [himageW] at hh
    exact (outer_elementary_card_lt hn (A.map f) hout).not_ge hh
  have hWJ : W ≤ Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q) := by
    obtain ⟨A,hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (⊤:Subgroup Q)
    let : IsElementaryAbelian 2 A := hA.2.1
    let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    apply Stellmacher.elementary_le_maxJ_of_image_bound ⊤ A W f hA le_top (hWC A) hWker
    rw [hcardW]
    exact elementary_card_le (by omega) (A.map f)
  have hJmap : (Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q)).map Q.subtype =
      Stellmacher.elementaryAbelianMaxJ Q := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective Q.subtype Q.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hPJ : U ≤ Stellmacher.elementaryAbelianMaxJ Q := by
    have hh := map_mono (f:=Q.subtype) hWJ
    rwa [map_subgroupOf_eq_of_le hPQ,hJmap] at hh
  have hJQ : Stellmacher.elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  apply sylowNormalizer_le_normalizer_of_inner_action L (Stellmacher.elementaryAbelianMaxJ Q)
    (hQ.to_le hJQ) (hJQ.trans hQL) P hPJ
  intro j
  have hj : (⟨j,hJQ j.property⟩:Q) ∈ Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q) := by
    have hh : (j:G) ∈ (Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q)).map Q.subtype :=
      hJmap.symm ▸ j.property
    obtain ⟨x,hx,he⟩ := hh
    exact (show x=(⟨j,hJQ j.property⟩:Q) from Subtype.ext he) ▸ hx
  have hi : f ⟨j,hJQ j.property⟩ ∈ inner (BinaryField n) := by
    have hle : Stellmacher.elementaryAbelianMaxJ (⊤:Subgroup Q) ≤ (inner (BinaryField n)).comap f :=
      sSup_le fun A hA => map_le_iff_le_comap.mp (hinnerA A hA)
    exact hle hj
  obtain ⟨l,hl⟩ := hi
  exact (MulAut.congr_inner_iff e _).mp ⟨l,hl.symm⟩

/-- Every binary linear component of degree greater than two has its Borel
normalizing the original Thompson subgroup, including exchanged pairs. -/
theorem component_normalizer_thompson
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : Theory.GroupTheory.IsComponent H (L.subgroupOf H)) (hS : IsPGroup 2 S)
    (hi : (normalizer (L:Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    {n : ℕ} (hn : 2<n) (e : L ≃* BinaryGroup n) :
    (normalizer (P : Set L)).map L.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ S : Set G) := by
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eP : P ≃* R := e.subgroupMap (P : Subgroup L)
  let : IsElementaryAbelian 2 R := sylow_elementary R
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  have hcardP : Nat.card P=2^n := (Nat.card_congr eP.toEquiv).trans
    ((sylow_card R).trans (GaloisField.card 2 n (by omega)))
  have hp : 2<Nat.card P := by
    rw [hcardP]
    exact (by decide : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  have hz : center L=⊥ := by
    apply bot_unique
    intro l hl
    have hh : e l ∈ center (BinaryGroup n) := (centerCongr e ⟨l,hl⟩).property
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  have hb (D : Subgroup (MulAut L)) (hD : IsElementaryAbelian 2 D) : Nat.card D ≤ Nat.card P := by
    let := hD
    let eA := MulAut.congr e
    let : IsElementaryAbelian 2 (D.map eA.toMonoidHom) := IsElementaryAbelian.map eA.toMonoidHom
    have hh := elementary_card_le (by omega : 2≤n) (D.map eA.toMonoidHom)
    rwa [card_map_of_injective eA.injective,←hcardP] at hh
  have hJN := hL.maxJ_normalizes_of_elementary_sylow_bound H L S hLH hSH hz hi P hPS hp hb
  let Q := S ⊓ normalizer (L:Set G)
  have hJ : Stellmacher.elementaryAbelianMaxJ Q=Stellmacher.elementaryAbelianMaxJ S :=
    Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate S Q
      (le_inf (sSup_le fun _ hA => hA.1) hJN) inf_le_left
  rw [←hJ]
  exact normalizing_thompson L Q (hS.to_le inf_le_left) inf_le_right P
    (le_inf hPS ((map_subtype_le _).trans L.le_normalizer)) hn e

/-- The same theorem over the caller's finite field and actual model equivalence. -/
theorem component_normalizer_thompson_field
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : Theory.GroupTheory.IsComponent H (L.subgroupOf H)) (hS : IsPGroup 2 S)
    (hi : (normalizer (L:Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    {n : ℕ} (hn : 2<n) (hF : Nat.card F=2^n) (e : L ≃* PSL(2,F)) :
    (normalizer (P : Set L)).map L.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ S : Set G) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (BinaryField n) := Fintype.ofFinite _
  let eF : F ≃+* BinaryField n := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card,Fintype.card_eq_nat_card,hF,
      GaloisField.card 2 n (by omega)])
  exact component_normalizer_thompson H L S hLH hSH hL hS hi P hPS hn
    (e.trans (Atlas.fieldEquivPSL 2 eF))

end Theory.PSL2.OrdinaryBorel
