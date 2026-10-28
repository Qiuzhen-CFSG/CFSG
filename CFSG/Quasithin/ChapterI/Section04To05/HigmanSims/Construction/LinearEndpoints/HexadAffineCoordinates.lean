module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadSplitting
public import Theory.SpecificGroups.SymmetricSix.PolarAffine

/-!
# Actual affine coordinates on the split hexad overgroup

The complement constructed from the original paired radicals is fed to the
literal polar affine model.  The resulting equivalence keeps the original
quotient map, the original full elementary kernel coordinates, and the actual
complement pointwise in the quotient factor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule
local notation "Model" => Theory.SpecificGroups.SymmetricSix.PolarAffine.Model

/-- The actual hexad extension has literal affine coordinates retaining all
source maps.  No abstract extension or recognition input is used: `q`, its
kernel coordinates, and the complement are the maps constructed from the
original endpoint and opposite radical. -/
theorem TypeAt.hexad_affine_coordinates (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W≤V) (hW4 : Nat.card W=4) (hWA : W≤A)
    (hAC : A≤centralizer (W:Set G)) (hAP : A⊓(normalizer (V:Set G)).pCoreIn 2=W)
    (c : G) (hc : c∈(normalizer (V:Set G)).pCoreIn 2) (hcW : c^2∉W)
    (hB : B=A.map (MulAut.conj c).toMonoidHom) (hi : A⊓B=W)
    (d : NaturalEndpointData A) (hBd : B≤d.carrier)
    (L : Subgroup G) (hPL : d.carrier≤L) (eL : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map eL.toMonoidHom=Point)
    (hB16 : Nat.card B=16) :
    ∃ hDN : d.hexad_overgroup≤normalizer (A:Set G),
      ∃ q : d.hexad_overgroup→*A6, Function.Surjective q ∧
        ∃ hker : q.ker=A.subgroupOf d.hexad_overgroup,
          (∀ g : d.hexad_overgroup, (q g:Equiv.Perm (Fin 6))=
            d.six_letter_quotient (inclusion hDN g)) ∧
          ∃ kA : q.ker≃*Multiplicative Vec,
            (∀ a : q.ker, (kA a).toAdd=d.binary_coordinates
              (Additive.ofMul ⟨((a:d.hexad_overgroup):G), by
                exact (show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup
                  from hker ▸ a.property)⟩)) ∧
            (∀ (g : d.hexad_overgroup) (a : q.ker),
              kA (MulAut.conjNormal g a)=Multiplicative.ofAdd
                (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val
                  (kA a).toAdd)) ∧
            ∃ K : Subgroup d.hexad_overgroup, q.ker.IsComplement' K ∧
              ∃ e : d.hexad_overgroup≃*Model,
                (∀ g, (e g).right=q g) ∧
                (∀ a : q.ker, e a=SemidirectProduct.inl (kA a)) ∧
                (∀ x : K, e x=SemidirectProduct.inr (q x)) := by
  obtain ⟨hDN,q,hq,hker,hqmark,kA,hkA,hkact⟩ :=
    d.hexad_kernel_coordinates L hPL eL hmark
  obtain ⟨hDN',q',hq',hker',hmark',K,hK,_⟩ := h.hexad_kernel_complement
    W A B hWV hW4 hWA hAC hAP c hc hcW hB hi d hBd L hPL eL hmark hB16
  have hqeq : q'=q := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (hmark' g).trans (hqmark g).symm
  have hKq : q.ker.IsComplement' K := hqeq ▸ hK
  obtain ⟨e,heq,hkercoord,hKcoord,_⟩ :=
    Theory.SpecificGroups.SymmetricSix.PolarAffine.exists_original_coordinates
      q hq kA (by
        intro g a
        simpa only [Theory.SpecificGroups.SymmetricSix.PolarAffine.action_apply]
          using hkact g a) K hKq
  exact ⟨hDN,q,hq,hker,hqmark,kA,hkA,hkact,K,hKq,e,heq,hkercoord,hKcoord⟩

end CFSG.Quasithin.HigmanSims
