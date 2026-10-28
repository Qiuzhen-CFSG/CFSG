module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingActionMarking
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup
/-!
# The original alternating-five Borel

The selected single block is the actual two-residual. Its marked natural
quotient therefore maps onto A₅ inside the symmetric-five action on H.
The maximal intersection M∩H contains a Sylow two-subgroup and the kernel,
so its image is a point stabilizer S₄. Its literal intersection with the
block consequently has the A₄ point-stabilizer image.

The core theorem also removes the possible central excess from O₂(L),
using the original C.5 source core identity. These are the extension and
Borel marks for the extraspecial residual calculation in 2.4.29.

Source: Aschbacher–Smith, 2.4.5(4) and 2.4.29, printed pp.528,544–545.
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_block_core_intrinsic_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) :
    pCore 2 d.block = blockU d.block := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let U := (blockU d.block).map d.block.subtype
  let : U.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  have hU0 : d.U0 = U := by
    apply le_antisymm
    · apply iSup_le
      intro s
      exact (mem_normalizer_iff_map_conj_eq.mp
        (show (s : d.H) ∈ normalizer (U : Set d.H) from by
          rw [normalizer_eq_top]; trivial)).le
    · exact le_iSup_of_le (1 : (d.S : Subgroup d.H)) (by
        intro u hu
        exact mem_map.mpr ⟨u,hu,by simp⟩)
  have hc := (d.core_source hG T hST).1
  rw [hsingle,hU0] at hc
  exact (map_injective d.block.subtype_injective hc).symm

theorem MinimalBlockSetup.single_alternating_residual_action
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (q : d.H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 d.H) :
    d.block.map q = alternatingGroup (Fin 5) ∧
      (q.comp d.block.subtype).ker = pCore 2 d.block := by
  let hnormal : d.block.Normal := hsingle ▸ d.L0_normal
  constructor
  · rw [←hsingle,d.L0_eq_residual,map_pResidual_of_surjective 2 q hq,
      Equiv.Perm.twoResidual_eq_alternating]
  · change q.ker.subgroupOf d.block = pCore 2 d.block
    rw [hker]
    exact hnormal.isSubnormal.pCore_subgroupOf 2

/-- The natural action marks the original maximal intersection and its block Borel. -/
theorem MinimalBlockSetup.single_alternating_borel_action
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    ∃ (q : d.H →* Equiv.Perm (Fin 5))
      (e : (blockU d.block).map d.block.subtype ≃*
        Multiplicative (core (Fin 5))) (i : Fin 5),
      Function.Surjective q ∧ q.ker = pCore 2 d.H ∧
      d.block.map q = alternatingGroup (Fin 5) ∧
      (q.comp d.block.subtype).ker = pCore 2 d.block ∧
      (M.subgroupOf d.H).map q = MulAction.stabilizer (Equiv.Perm (Fin 5)) i ∧
      ((M.subgroupOf d.H) ⊓ d.block).map q =
        alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 5)) i ∧
      Nat.card (((M.subgroupOf d.H) ⊓ d.block).map q) = 12 ∧
      ∀ (s : d.H) (u : (blockU d.block).map d.block.subtype),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : d.H) =
            s * (u : d.H) * s⁻¹ := by
  obtain ⟨q,e,hq,hker,_,he⟩ := d.single_alternating_marked_action hsingle hA
  have hres := d.single_alternating_residual_action hsingle q hq hker
  have hSB : (d.S : Subgroup d.H) ≤ M.subgroupOf d.H := by
    intro s hs
    exact d.full_pair.1.1.2.1 (mem_map_of_mem d.H.subtype hs)
  have hkB : q.ker ≤ M.subgroupOf d.H :=
    hker.le.trans ((pCore_isPGroup.le_sylow_of_normal d.S).trans hSB)
  obtain ⟨i,hi,hB,hcard⟩ :=
    Theory.SpecificGroups.SymmetricFive.SylowOvergroup.quotient_borel
      q hq d.S (M.subgroupOf d.H) d.block hSB d.intersection_maximal hkB hres.1
  exact ⟨q,e,i,hq,hker,hres.1,hres.2,hi,hB,hcard,he⟩
/-- The actual block extension and its literal A₄ Borel, with full natural coordinates. -/
theorem MinimalBlockSetup.single_alternating_block_borel_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    ∃ (q : d.block →* alternatingGroup (Fin 5))
      (e : blockU d.block ≃* Multiplicative (core (Fin 5))) (i : Fin 5),
      Function.Surjective q ∧ q.ker = blockU d.block ∧
      (M.subgroupOf d.H).subgroupOf d.block =
        (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap q ∧
      ∀ (s : d.block) (u : blockU d.block),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s : Equiv.Perm (Fin 5)) (e u).toAdd)) : d.block) =
            s * (u : d.block) * s⁻¹ := by
  obtain ⟨q,e,i,hq,hker,hL,hkerL,hB,_,_,he⟩ := d.single_alternating_borel_action hsingle hA
  let p : d.block →* alternatingGroup (Fin 5) :=
    (q.comp d.block.subtype).codRestrict _ (fun l => hL ▸ mem_map_of_mem q l.property)
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨l,hl,hla⟩ := mem_map.mp (show (a : Equiv.Perm (Fin 5)) ∈ d.block.map q from hL.symm ▸ a.property)
    exact ⟨⟨l,hl⟩,Subtype.ext hla⟩
  have hkp : p.ker = blockU d.block := by
    have hker' : p.ker = (q.comp d.block.subtype).ker := by
      ext l
      exact Subtype.ext_iff
    rw [hker',hkerL,d.single_block_core_intrinsic_source hG T hST hsingle]
  let E := (blockU d.block).equivMapOfInjective d.block.subtype d.block.subtype_injective
  let e' : blockU d.block ≃* Multiplicative (core (Fin 5)) := E.trans e
  have hSB : (d.S : Subgroup d.H) ≤ M.subgroupOf d.H := by
    intro s hs
    exact d.full_pair.1.1.2.1 (mem_map_of_mem d.H.subtype hs)
  have hkB : q.ker ≤ M.subgroupOf d.H :=
    hker.le.trans ((pCore_isPGroup.le_sylow_of_normal d.S).trans hSB)
  have hpre : (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap q = M.subgroupOf d.H := by
    rw [←hB,comap_map_eq_self hkB]
  refine ⟨p,e',i,hp,hkp,?_,?_⟩
  · ext l
    change (l : d.H) ∈ M.subgroupOf d.H ↔ (p l : Equiv.Perm (Fin 5)) i = i
    rw [←hpre]
    rfl
  · intro s u
    apply Subtype.ext
    have hev (w : Multiplicative (core (Fin 5))) :
        ((e'.symm w : blockU d.block) : d.H) =
          (e.symm w : (blockU d.block).map d.block.subtype) := by
      have hw : E (e'.symm w) = e.symm w := by
        apply e.injective
        change e' (e'.symm w) = e (e.symm w)
        rw [e'.apply_symm_apply,e.apply_symm_apply]
      exact congrArg Subtype.val hw
    exact (hev _).trans (he (s : d.H) (E u))

end CFSG.Quasithin.Chapter2
