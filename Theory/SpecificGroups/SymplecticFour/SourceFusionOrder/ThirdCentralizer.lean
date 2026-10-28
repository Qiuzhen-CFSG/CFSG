module
public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Stellmacher.OmegaOneCenterMap

/-!
# A two-core criterion for the third involution centralizer

Let T be an ambient Sylow two-subgroup contained in C, with elementary
abelian center. Suppose the two-core Q of C is self-centralizing in C,
and each noncentral involution centralizer in T is one of a family of
commutative wings. Then C is contained in D if the Sylow-center normalizer
and the intersections of C with the wing normalizers are contained in D.

Indeed Z(T) lies in E = Ω₁(Z(Q)). If E is Z(T), its normalizer gives the
bound. Otherwise a noncentral involution in E puts Q in a wing; the
self-centralizing condition gives the reverse inclusion. The normalizer
of this wing now gives the bound. A separate Burnside-fusion lemma supplies
the Sylow-center normalizer bound from control of central subgroups.

These are the group-theoretic steps in Aschbacher–Smith F.4.39, printed
p.294 of `refs/quasithin.pdf`. The source application must first establish
that the inner Sylow is an ambient Sylow; that transfer is not assumed
proved here.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A self-centralizing two-core and commutative noncentral involution
centralizers reduce containment to the Sylow-center and wing normalizers. -/
theorem le_of_noncentral_involution_centralizers
    (T : Sylow 2 G) (C D : Subgroup G)
    (hTC : (T : Subgroup G) ≤ C)
    (hself : C ⊓ centralizer (C.pCoreIn 2 : Set G) ≤ C.pCoreIn 2)
    (hZ : IsElementaryAbelian 2 (center T))
    {ι : Type*} (R : ι → Subgroup T)
    (hR : ∀ i, IsMulCommutative (R i))
    (hcent : ∀ e : T, e^2=1 → e ∉ center T →
      ∃ i, centralizer ({e} : Set T) = R i)
    (hNZ : normalizer ((center T).map (T : Subgroup G).subtype : Set G) ≤ D)
    (hNR : ∀ i, C ⊓ normalizer ((R i).map (T : Subgroup G).subtype : Set G) ≤ D) :
    C ≤ D := by
  let Q := C.pCoreIn 2
  let E := Stellmacher.omegaOneCenterAmbient Q
  let Z := (center T).map (T : Subgroup G).subtype
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow C (T.subtype hTC)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTC] at hh
  have hCNQ : C ≤ normalizer (Q : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCNE : C ≤ normalizer (E : Set G) := by
    let K : Subgroup Q :=
      (omega₁ (G := center Q) (p := 2)).map (center Q).subtype
    let _ : (omega₁ (G := center Q) (p := 2)).Characteristic := omega₁_characteristic (center Q)
    have hK : K.Characteristic := inferInstance
    let _ : K.Characteristic := hK
    exact hCNQ.trans (normalizer_le_normalizer_characteristic_image Q K)
  have hZE : Z ≤ E := by
    rintro _ ⟨z,hz,rfl⟩
    have hzQ : z.val ∈ Q := hself ⟨hTC z.property, by
      intro q hq
      exact congrArg (fun t : T => t.val) ((mem_center_iff.mp hz) ⟨q,hQT hq⟩)⟩
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff Q z.val).mpr
    exact ⟨hzQ,congrArg (fun t : T => t.val)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz),fun q hq =>
      congrArg (fun t : T => t.val) ((mem_center_iff.mp hz) ⟨q,hQT hq⟩)⟩
  by_cases hEZ : E ≤ Z
  · have heq : E = Z := le_antisymm hEZ hZE
    exact hCNE.trans (heq ▸ hNZ)
  · obtain ⟨e,heE,heZ⟩ := SetLike.not_le_iff_exists.mp hEZ
    obtain ⟨heQ,he2,hecomm⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff Q e).mp heE
    let eT : T := ⟨e,hQT heQ⟩
    have heT2 : eT^2=1 := Subtype.ext he2
    have heTZ : eT ∉ center T := fun hz => heZ (mem_map_of_mem _ hz)
    obtain ⟨i,hi⟩ := hcent eT heT2 heTZ
    let A := (R i).map (T : Subgroup G).subtype
    have hQA : Q ≤ A := by
      intro q hq
      refine ⟨⟨q,hQT hq⟩,?_,rfl⟩
      rw [←hi]
      apply mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (hecomm q hq)
    have hAQ : A ≤ Q := by
      rintro _ ⟨a,ha,rfl⟩
      refine hself ⟨hTC a.property,?_⟩
      intro q hq
      obtain ⟨b,hb,hbq⟩ := hQA hq
      let _ := hR i
      have hh := mul_comm (⟨b,hb⟩ : R i) ⟨a,ha⟩
      exact hbq ▸ congrArg (fun t : R i => t.val.val) hh
    have hQ : Q = A := le_antisymm hQA hAQ
    intro c hc
    apply hNR i
    refine ⟨hc,?_⟩
    change c ∈ normalizer (A : Set G)
    rw [←hQ]
    exact hCNQ hc

/-- Burnside fusion promotes normalizer control of a central subgroup
from the Sylow normalizer to the whole Sylow-center normalizer. -/
theorem center_normalizer_le_of_sylow_normalizer_le
    (T : Sylow 2 G) (R : Subgroup G)
    (hRZ : R ≤ (center T).map (T : Subgroup G).subtype)
    (hNR : normalizer (T : Set G) ≤ normalizer (R : Set G)) :
    normalizer ((center T).map (T : Subgroup G).subtype : Set G) ≤
      normalizer (R : Set G) := by
  let Z := (center T).map (T : Subgroup G).subtype
  have hweak (g : G) (hg : (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ T) :
      g ∈ normalizer (T : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge hg
    rw [card_map_of_injective (MulAut.conj g).injective]
  have hZC : Z ≤ centralizer (T : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ t ht
    exact congrArg (fun t : T => t.val) ((mem_center_iff.mp hz) ⟨t,ht⟩)
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hyZ : g*x*g⁻¹ ∈ Z := (hg x).mp (hRZ hx)
  obtain ⟨a,ha,he⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
    (T : Subgroup G) le_rfl hweak (hZC (hRZ hx)) (hZC hyZ)
    (isConj_iff.mpr ⟨g,rfl⟩)
  rw [←he]
  exact (hNR ha x).mp hx
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
