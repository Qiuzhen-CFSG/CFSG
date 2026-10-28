module
public import Theory.SpecificGroups.Suzuki.InvolutionCentralizerSylow
public import Theory.SpecificGroups.SymplecticFour.SuzukiBorelPlacement
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SuzukiSubgroup
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MiddleRecognition
/-!
# The original Suzuki opposite-pair witness

A Suzuki model of the literal opposite pair supplies its prescribed Sylow
intersection: the selected original nonroot involution has centralizer P∩U,
and involutions in a Suzuki Sylow are central. Nontrivial Sylow squares then
force its normalizer into the original Borel. The same original component
inclusion transports the concrete Suzuki witness, including its internal
conjugator and quotient Borel marking. No intersection or representation
recognition assumption remains beyond the actual whole-pair Suzuki model.
Source: Aschbacher--Smith E.2.7, printed pp.220--221.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
open Structure.SymplecticFour
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem source_suzuki_pair_witness {n m : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hm : 0<m)
    (em : oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) ≃* SuzukiMatrixGroup m) :
    Nonempty (BenderPlacement.OriginalWitness T (ChapterB.minimalParabolicMax T hP) V (2*m+1)) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  let P := oppositePair W
  let K := P.map f
  let d : P ≃* K := P.equivMapOfInjective f (L.subtype_injective.comp e.injective)
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,_⟩ := source_geometry hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  obtain ⟨z,hzV,hz2,hzC⟩ := source_nonroot_component_centralizer hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hzW : e.symm z ∈ W := by
    change (e (e.symm z) : G) ∈ V
    simpa using hzV
  let zP : P := ⟨e.symm z,(show W≤P from le_sup_left) hzW⟩
  have hC : centralizer ({zP} : Set P) = (unipotent (F := F)).subgroupOf P := by
    ext x
    rw [mem_centralizer_singleton_iff,mem_subgroupOf,←hmark]
    change x*zP=zP*x ↔ (e (x : Sp F) : G) ∈ (T : Subgroup G)
    rw [← show e (x : Sp F) ∈ (T : Subgroup G).subgroupOf L ↔
      (e (x : Sp F) : G) ∈ (T : Subgroup G) from Iff.rfl,←hzC,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hh := congrArg (fun a : P => e (a : Sp F)) hx
      simpa only [Subgroup.coe_mul,map_mul,zP,MulEquiv.apply_symm_apply] using hh
    · intro hx
      apply Subtype.ext
      apply e.injective
      simpa only [Subgroup.coe_mul,map_mul,zP,MulEquiv.apply_symm_apply] using hx
  have hzsq : zP^2=1 := by
    apply Subtype.ext
    apply e.injective
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one,zP,
      MulEquiv.apply_symm_apply,hz2] using (pow_orderOf_eq_one z : z^orderOf z=1)
  obtain ⟨S,hS⟩ := suzuki_sylow_of_involution_centralizer hm em zP hzsq
    (hC.symm ▸ (isPGroup_unipotent hF).comap_subtype)
  have hSU : (S : Subgroup P)=(unipotent (F := F)).subgroupOf P := hS.trans hC
  have hB : normalizer ((unipotent (F := F)).subgroupOf P : Set P) = borel.subgroupOf P := by
    apply le_antisymm
    · rw [←hSU]
      exact suzuki_sylow_normalizer_le_borel P hm em S hSU.le
    · intro x hx
      apply mem_normalizer_iff.mpr
      intro y
      have hb := mem_normalizer_iff.mp (borel_le_normalizer_unipotent hx) (y : Sp F)
      exact hb
  let R := S.mapSurjective (f := d.toMonoidHom) d.surjective
  have hR : (R : Subgroup K)=(T : Subgroup G).subgroupOf K := by
    change (S : Subgroup P).map d.toMonoidHom = _
    have hh : ((T : Subgroup G).subgroupOf K).comap d.toMonoidHom = S := by
      ext x
      rw [hSU,mem_subgroupOf,←hmark]
      rfl
    rw [←hh,map_comap_eq_self_of_surjective d.surjective]
  have hBm : (borel.subgroupOf P).map d.toMonoidHom =
      (ChapterB.minimalParabolicMax T hP).subgroupOf K := by
    have hh : ((ChapterB.minimalParabolicMax T hP).subgroupOf K).comap d.toMonoidHom =
        borel.subgroupOf P := by
      ext x
      rw [mem_subgroupOf,←source_borel_intersection hF hn T hP L e hmark hgen]
      rfl
    rw [←hh,map_comap_eq_self_of_surjective d.surjective]
  have hMR : (ChapterB.minimalParabolicMax T hP).subgroupOf K=normalizer (R : Set K) := by
    rw [←hBm,←hB,←hSU,map_normalizer_eq_of_bijective _ d.bijective]
    rfl
  have hVK : V≤K := by
    rw [←hmap]
    exact map_mono le_sup_left
  have hrank : 1<primeRank 2 V := by
    by_contra hn
    have ht : IsElementaryAbelian 2 (⊤ : Subgroup V) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup V).subtype Subtype.val_injective
    have hh := (primeRank_le_iff_elementary_card_le V).mp (Nat.le_of_not_gt hn) ⊤ ht
    rw [card_top,pow_one] at hh
    omega
  exact BenderPlacement.suzuki_subgroup_witness T _ K V hm (d.symm.trans em)
    R hR hMR hVK hVT hrank

/-- The literal Suzuki pair discharges the E2.13 recognized-pair alternative. -/
theorem source_hasRecognizedPair_of_suzuki_pair {n m : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hm : 0<m)
    (em : oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) ≃* SuzukiMatrixGroup m) :
    HasRecognizedPair T (ChapterB.minimalParabolicMax T hP) V := by
  obtain ⟨w⟩ := source_suzuki_pair_witness hF hn T hP hJ L e hmark hgen
    V hVT hVM hVN hr hm em
  exact HasRecognizedPair.of_originalWitness w

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
