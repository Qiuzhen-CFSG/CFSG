module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import Theory.Representation.SL2NaturalOffenders.NaturalPair.Dimensions
/-!
# Order of alpha in the original paired natural source

If the prescribed Sylow has no nontrivial residual centralizer, the source
paired quotient has zero kernel. Its two natural planes give module rank
4n and the sharp Thompson fixed codimension gives 2n. E.2.3 identifies
alpha with that fixed subgroup, hence its order is the square of the
actual defining field order. All maps and the prescribed exchange remain
those of the original marked source.

Source: Aschbacher--Smith B.6.10 and E.2.3(2), pp.117 and216--217,
used in 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false in
theorem source_alpha_card_of_trivial_sylow_residual_centralizer
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (hz : (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) = ⊥) :
    Nat.card (thompsonAlpha (T : Subgroup G)) = Nat.card F.Carrier ^ 2 := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hαT : thompsonAlpha (T : Subgroup G) ≤ T := by
    intro x hx
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    exact hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hcentral : thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hαT).trans_eq hz)
  have hα := (source_global_baumann_and_alpha T hP U hU hJ q hq hk d F c hexchange).2
  rw [hcentral,bot_sup_eq] at hα
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hf
  have hker := source_offender_pair_linear_kernel α (T.mapSurjective hq) hp hff hcore F c
  rw [←map_pResidual_of_surjective 2 q hq] at hker
  have hinj : Function.Injective c.quotientMap := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hvc := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (pResidual 2 G) v).mp
      (hker ▸ hv)
    have he := mem_bot.mp (hz ▸ (show (v.toMul:G) ∈
      (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) from ⟨hUT v.toMul.property,hvc⟩))
    change v = 0
    exact Additive.toMul.injective (Subtype.ext he)
  let f := LinearEquiv.ofBijective c.quotientMap ⟨hinj,c.quotientMap_surjective⟩
  have hdim : Module.finrank (ZMod 2) (Additive U) = 4 * Module.finrank (ZMod 2) F.Carrier := by
    calc
      _ = Module.finrank (ZMod 2) ((Fin 2 → F.Carrier) × (Fin 2 → F.Carrier)) := f.finrank_eq
      _ = _ := by simp [Module.finrank_prod,Module.finrank_pi_fintype]; omega
  obtain ⟨ρ,hρ,hnat,he,⟨hJq,_⟩,hfix⟩ :=
    source_images_and_fixedSpace T hP U hU hJ q hq hk d F c hexchange
  have hcod : fixedCodim α ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
      2 * Module.finrank (ZMod 2) F.Carrier := by
    rw [SL2NaturalOffenders.fixedCodim_eq_of_fixedSpace_comap α ρ c.quotientMap
      c.quotientMap_surjective _ hfix,hJq]
    obtain ⟨P,hPa⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
    change (P : Subgroup Y).map Y.subtype = (T : Subgroup G).map q ⊓ Y at hPa
    rw [←hPa]
    exact SL2NaturalOffenders.paired_sylowImage_fixedCodim Y c.action.groupEquiv ρ hnat P
  have hrank : Module.finrank (ZMod 2)
      (fixedSpace α ((elementaryAbelianMaxJ (T : Subgroup G)).map q)) =
      2 * Module.finrank (ZMod 2) F.Carrier := by
    have hh := fixedCodim_add_finrank α ((elementaryAbelianMaxJ (T : Subgroup G)).map q)
    rw [hcod,hdim] at hh
    omega
  rw [hα,←Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q hq hk
    (elementaryAbelianMaxJ (T : Subgroup G)))]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hrank]
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod] at hF
  rw [hF,←pow_mul,mul_comm 2]
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
