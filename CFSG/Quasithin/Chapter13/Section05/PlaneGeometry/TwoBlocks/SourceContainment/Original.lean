module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Source
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Source

/-!
# Original contrary-plane inputs to the13.5.6 contradiction

The genuine nonisotropic conjugate supplies the A₆ block internally. Its
literal plane residual has nonabelian two-core and is normalized by the full
plane normalizer once13.3.14 is supplied. The original module centralizer
lies in M by uniqueness. The independent two-A₃ residual calculation is
reexported for the next containment step; no X-conjugate containment is
asserted here.

Source: Aschbacher--Smith13.5.4(6) and13.5.6(2), printed pp.916–917.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_nonisotropic_planeActor
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (x:G)(hWV:V₂.map (MulAut.conj x).toMonoidHom≤V)
    (hn:¬∀v∈image d (V₂.map (MulAut.conj x).toMonoidHom),
      ∀w∈image d (V₂.map (MulAut.conj x).toMonoidHom),form v w=0)
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    ⁅V,planeActor (L:=L) (V₂:=V₂)⁆=V ∧
      V≤(planeActor (L:=L) (V₂:=V₂)).pCoreIn 2 ∧
      ¬IsMulCommutative (pCore 2 (planeActor (L:=L) (V₂:=V₂))) ∧
      normalizer (V₂:Set G)≤normalizer (planeActor (L:=L) (V₂:=V₂):Set G) ∧
      centralizer (V:Set G)≤M := by
  have hb:=(source_block_of_nonisotropic_conjugate d hu x hWV hn).1
  obtain ⟨hgen,hcore,hna⟩:=source_planeActor_nonabelian_core d hb
  exact ⟨hgen,hcore,hna,source_planeActor_normalized d hb hm,source_module_centralizer_le d hu⟩

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
