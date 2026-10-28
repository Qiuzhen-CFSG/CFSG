module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The central orbit at the start of the MS argument

Let R contain the two-core Q of a group of characteristic two, and let W
be the normal closure of Ω₁(Z(R)). Then W lies in Ω₁(Z(Q)), so is elementary
abelian. If G=KR and the MS characteristic condition holds, K moves W:
otherwise Ω₁(Z(R)) would be central in G and contradict that condition.

For normal K with simple K/O₂(K), the centralizer of W meets K in O₂(K).
Its kernel and image under G → G/K are two-groups, so C_G(W)=Q. This gives
the initial faithful module layer without a natural-module or whole-core
reconstruction assumption.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and the opening
module reduction in Meierfrankenfeld--Stellmacher, "Pushing up weak BN-pairs
of rank two" (1993). The subsequent identification of [O₂(K),K] remains
separate from this initial-layer result.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The normal closure of the actual Sylow-center omega subgroup. -/
abbrev omegaOrbit (R : Subgroup G) : Subgroup G :=
  normalClosure (omegaCenterIn R : Set G)

omit [Finite G] in
private theorem omega_normal (Q : Subgroup G) [Q.Normal] :
    (omegaCenterIn Q).Normal := by
  let : (omega₁ (center Q) (p := 2)).Characteristic := omega₁_characteristic _
  infer_instance

private theorem omega_ne_bot (R : Subgroup G) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    omegaCenterIn R ≠ ⊥ := by
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
  have hz := omega_center_ne_bot hp
  intro hh
  exact hz ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp hh)

omit [Finite G] in
/-- The actual Sylow-center orbit lies in the central omega of the two-core. -/
theorem omegaOrbit_le_centralOmega (R : Subgroup G)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    omegaOrbit R ≤ omegaCenterIn (pCore 2 G) := by
  let := omega_normal (pCore 2 G)
  apply normalClosure_le_normal
  intro x hx
  obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff R x).mp hx
  have hcx := centralizer_le hQR hc
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨hself hcx,hcx,hp⟩

omit [Finite G] in
/-- The orbit is a genuine elementary subgroup, before module recognition. -/
theorem omegaOrbit_elementary (R : Subgroup G)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    IsElementaryAbelian 2 (omegaOrbit R) :=
  IsElementaryAbelian.of_le (omegaOrbit_le_centralOmega R hQR hself)

/-- MS3 forces the component to move the original central orbit. -/
theorem component_not_centralizes_omegaOrbit (K R : Subgroup G)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ r ∈ R, k*r=g)
    (hms : MSCharacteristicCondition R) : ¬ K ≤ centralizer (omegaOrbit R : Set G) := by
  intro hc
  have hZK : omegaCenterIn R ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp ((centralizer_le (subset_normalClosure :
      omegaCenterIn R ≤ omegaOrbit R)).trans' hc)
  have hz : omegaCenterIn R ≤ center G := by
    intro z hz
    rw [mem_center_iff]
    intro g
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod g
    have hkz := hZK hz k hk
    have hrz := ((mem_omegaCenterIn_iff R z).mp hz).2.1 r hr
    calc k*r*z = k*(r*z) := mul_assoc _ _ _
      _ = k*(z*r) := by rw [hrz]
      _ = (k*z)*r := (mul_assoc _ _ _).symm
      _ = (z*k)*r := by rw [hkz]
      _ = z*(k*r) := mul_assoc _ _ _
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  have hn : (C.map R.subtype).Normal := ⟨by
    intro z hzC g
    have he := mem_center_iff.mp (hz hzC) g
    simpa only [he, mul_inv_cancel_right] using hzC⟩
  have hbot := hms.eq_bot_of_normal C hn
  apply omega_ne_bot R hp hne
  change C.map R.subtype = ⊥
  rw [hbot,Subgroup.map_bot]

/-- For a normal component with simple two-core quotient, MS3 makes the
central orbit faithful modulo the ambient two-core. -/
theorem omegaOrbit_centralizer (K R : Subgroup G) [K.Normal]
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 G ≤ R)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ r ∈ R, k*r=g)
    (hms : MSCharacteristicCondition R) :
    centralizer (omegaOrbit R : Set G) = pCore 2 G := by
  let W := omegaOrbit R
  let C := centralizer (W : Set G)
  have hQC : pCore 2 G ≤ C := by
    intro q hq w hw
    exact (((mem_omegaCenterIn_iff _ _).mp
      (omegaOrbit_le_centralOmega R hQR hself hw)).2.1 q hq).symm
  have hQKQ : (pCore 2 K).map K.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  let D := C.subgroupOf K
  let qK := QuotientGroup.mk' (pCore 2 K)
  have hQD : pCore 2 K ≤ D := fun x hx => hQC (hQKQ (mem_map_of_mem K.subtype hx))
  have hDK : D ≤ pCore 2 K := by
    let : D.Normal := inferInstance
    have hn : (D.map qK).Normal := Normal.map inferInstance qK (QuotientGroup.mk'_surjective _)
    rcases hn.eq_bot_or_eq_top with hz | ht
    · simpa only [qK,QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hz
    · have hDtop : D = ⊤ := by
        have he := congrArg (fun A => A.comap qK) ht
        simpa only [comap_map_eq,qK,QuotientGroup.ker_mk',sup_eq_left.mpr hQD,comap_top] using he
      exfalso
      apply component_not_centralizes_omegaOrbit K R hp hne hprod hms
      intro k hk
      exact (show (⟨k,hk⟩ : K) ∈ D from hDtop ▸ mem_top _)
  let q := QuotientGroup.mk' K
  have hqR : Function.Surjective (q.comp R.subtype) := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod g
    refine ⟨⟨r,hr⟩,?_⟩
    change q r = q (k*r)
    rw [map_mul,show q k=1 from (QuotientGroup.eq_one_iff _).mpr hk,one_mul]
  have hquot : IsPGroup 2 (G ⧸ K) := hp.of_surjective (q.comp R.subtype) hqR
  let f := q.comp C.subtype
  have hker : IsPGroup 2 f.ker := by
    let i : f.ker →* pCore 2 K := {
      toFun x := ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,
        hDK x.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact pCore_isPGroup.of_injective i (fun _ _ hh => Subtype.ext (Subtype.ext
      (congrArg (fun z : pCore 2 K => (z.val : G)) hh)))
  have hCp : IsPGroup 2 C := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup f hker
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  exact le_antisymm (le_sSup ⟨inferInstance,hCp⟩) hQC

end CFSG.Quasithin.ChapterC.MSCentralOrbit
