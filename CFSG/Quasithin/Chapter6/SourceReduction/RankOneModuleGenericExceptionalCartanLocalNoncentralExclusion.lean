module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentral
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer

/-!
# Excluding both original nonquasisimple Cartan containers

The source involution centralizer supplies a smaller residual E isomorphic
to prime-field SL₂, containing the image of the original residual and
normalized by the original Cartan intersection and full Sylow. Lift N(E)
through the literal quotient Y → Y/O₂(Y). Its image Y₀ in G contains the
original two-core and H, and A intersect Y₀ equals A intersect Y.

The perfect residual of the preimage of E is a normal C-component of Y₀.
Its literal quotient map has two-group kernel, so its intrinsic two-core
quotient is PSL₂(p). The already proved original prime-field exclusion
applies to Y₀ with the same Input, Cartan pair, original residual and escape.
This implements the smaller-container step in 5.1.13 and removes both
nonquasisimple alternatives without changing the selected original container.

Only the original binary-triality endpoint remains beside the complete
exceptional conclusion for the original whole W. Its ambient exclusion
and full SourceLocalCartanEscape assembly are still open.
Source: Aschbacher–Smith 5.1.13, printed p.636, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- Lift the actual smaller SL₂ residual to its normalizer preimage. The
prime-field exclusion applies to this H-overgroup and the same Cartan intersection. -/
theorem not_noncentral_cartan_section
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hs : NoncentralCartanSection T H A Y C) : False := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let I := C.map q
  obtain ⟨p,hp,hp3,f,hf,hker,z,hz,hfz,hzR,hzP,hfix,hRK,hlt,hn,⟨e,he⟩⟩ := hs
  let : Fact p.Prime := ⟨hp⟩
  let J := centralizer ({z} : Set I)
  let K := (solvableResidual J).map J.subtype
  let E := K.map I.subtype
  let eE : E ≃* SL(2,ZMod p) :=
    (K.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e
  let N := normalizer (E : Set (Y ⧸ pCore 2 Y))
  let U := N.comap q
  let Y₀ := U.map Y.subtype
  let ey : U ≃* Y₀ := U.equivMapOfInjective Y.subtype Y.subtype_injective
  have hY₀Y : Y₀ ≤ Y := map_subtype_le U
  have hQU : pCore 2 Y ≤ U := by
    intro x hx
    change q x ∈ N
    have hh : q x = 1 := (QuotientGroup.eq_one_iff (N := pCore 2 Y) x).mpr hx
    rw [hh]
    exact N.one_mem
  have hQY₀ : Y.pCoreIn 2 ≤ Y₀ := map_mono hQU
  have hY₀ : Y₀ ∈ Chapter1.H G := by
    intro hz
    apply hY.1
    have hc : Y.pCoreIn 2 ≤ Y₀.pCoreIn 2 := le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 Y) hQY₀ (hY₀Y.trans
        (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))
    exact le_bot_iff.mp (hz ▸ hc)
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRU : (residual H).subgroupOf Y ≤ U := by
    intro x hx
    exact E.le_normalizer (hRK (mem_map_of_mem q hx))
  have hRY₀ : residual H ≤ Y₀ := by
    have hh := map_mono (f := Y.subtype) hRU
    rwa [map_subgroupOf_eq_of_le hRY] at hh
  have hTY := hH.1.1.2.trans hY.2
  have hTY₀ : (T : Subgroup G) ≤ Y₀ := by
    intro x hx
    refine ⟨⟨x,hTY hx⟩,?_,rfl⟩
    exact hn (mem_sup_right (mem_map_of_mem q hx))
  have hHY₀ : H ≤ Y₀ := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le hRY₀ hTY₀
  have hDY₀ : A ⊓ Y ≤ Y₀ := by
    intro x hx
    refine ⟨⟨x,hx.2⟩,?_,rfl⟩
    exact hn (mem_sup_left (mem_map_of_mem q hx.1))
  let qU : U →* N := q.subgroupComap N
  have hqU : Function.Surjective qU :=
    q.subgroupComap_surjective_of_surjective N (QuotientGroup.mk'_surjective _)
  have hkU : IsPGroup 2 qU.ker := by
    have heq : qU.ker = q.ker.comap U.subtype := by
      ext x
      exact Subtype.ext_iff
    rw [heq,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent qU.ker := hkU.isNilpotent
  let : Group.IsSolvable qU.ker := inferInstance
  let EN := E.subgroupOf N
  have hENn : EN.Normal :=
    (normal_subgroupOf_iff_le_normalizer E.le_normalizer).mpr le_rfl
  let := hENn
  let eEN : EN ≃* SL(2,ZMod p) := (subgroupOfEquivOfLe E.le_normalizer).trans eE
  let : IsQuasisimple EN :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (by simpa using hp3) eEN
  have hEN : EN.IsCComponent :=
    (show IsComponent N EN from ⟨hENn.isSubnormal,inferInstance⟩).isCComponent
  let V := EN.comap qU
  let C₀ := (solvableResidual V).map V.subtype
  obtain ⟨hC₀,hm⟩ := cComponent_residual_preimage qU hqU hEN
  have hC₀n : C₀.Normal := ConjAct.normal_of_characteristic_of_normal
  let C₁ := C₀.map ey.toMonoidHom
  have hC₁ : C₁.IsCComponent := hC₀.map_equiv ey
  have hC₁n : C₁.Normal := Subgroup.Normal.map hC₀n ey.toMonoidHom ey.surjective
  have hCmap : C₁.map Y₀.subtype = (C₀.map U.subtype).map Y.subtype := by
    change (C₀.map ey.toMonoidHom).map Y₀.subtype = _
    rw [map_map C₀ Y₀.subtype ey.toMonoidHom, map_map C₀ Y.subtype U.subtype]
    rfl
  have hRV : ((residual H).subgroupOf Y).subgroupOf U ≤ V := by
    intro x hx
    exact hRK (mem_map_of_mem q hx)
  let : Group.IsPerfect (residual H) := Chapter1.mem_L_isPerfect hR
  let a := (subgroupOfEquivOfLe hRY).symm
  let : Group.IsPerfect ((residual H).subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let b := (subgroupOfEquivOfLe hRU).symm
  let : Group.IsPerfect (((residual H).subgroupOf Y).subgroupOf U) :=
    Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  have hRC₁ : residual H ≤ C₁.map Y₀.subtype := by
    rw [hCmap]
    have hh := map_mono (f := Y.subtype) (map_mono (f := U.subtype)
      (le_map_solvableResidual_of_isPerfect _ V hRV))
    rwa [map_subgroupOf_eq_of_le hRU,map_subgroupOf_eq_of_le hRY] at hh
  let eimg := (MulEquiv.subgroupCongr hm).trans eEN
  let f₀ := eimg.toMonoidHom.comp (qU.subgroupMap C₀)
  have hf₀ : Function.Surjective f₀ := eimg.surjective.comp (qU.subgroupMap_surjective C₀)
  have hk₀ : IsPGroup 2 f₀.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eimg.injective,ker_subgroupMap]
    exact hkU.comap_subtype
  let ec := C₀.equivMapOfInjective ey.toMonoidHom ey.injective
  let ecq := QuotientGroup.congr _ _ ec.symm (pCore_map_iso 2 ec.symm)
  let eq := ecq.trans (Theory.PSL2.primeSL2CoverCoreEquiv hp3 f₀ hf₀ hk₀)
  apply not_prime_container_of_residual h hH hgen c ⟨hY₀,hHY₀⟩
    (fun hnorm => hescape (fun x hx => hnorm ⟨hx.1,hDY₀ hx⟩)) hR C₁ hC₁ hC₁n hRC₁ hp
    (hp.odd_of_ne_two (by omega))
  exact ⟨ZMod p,inferInstance,inferInstance,by simp,⟨eq⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Both nonquasisimple rows are excluded through the actual smaller SL₂
residual. Only the original binary-triality configuration remains beside
the complete exceptional conclusion for the original whole module. -/
theorem localCartan_escape_binary_or_exceptional
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L W H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧ K = residual H ∧
          (K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) := by
  rcases localCartan_escape_binary_or_noncentral_section h hH hgen c hY hescape with hout |
    ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,hKR,halt⟩
  · exact .inl hout
  · rcases halt with hbin | ⟨_,hs⟩
    · exact .inr ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,hKR,hbin⟩
    · exact (LocalSieve.not_noncentral_cartan_section h hH hgen c hY hescape
        (hKR ▸ hKL) C hs).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
