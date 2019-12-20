module proof2 where

open import proof public

-- Corrolary 1.1.1 (FP for closed terms).

fpc : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e : Term ᴢ} {τ : τ ᴢ} {ℾ Σ₀} → ℾ ⊢ ø → ℾ ⊢ ø → Γ , Σ₀ ⊢ e ⦂ τ , zero → ⟨ ø , ø ⟩∈𝒢⟦ zero ː ℾ ⟧ → ⟨ ø ⊢ e , ø ⊢ e ⟩∈ℰ⟦ zero ː (zero ⟨⟨ τ ⟩⟩) ⟧
fpc a b e₁ e₂ = fp a b e₁ e₂

∣_-_∣ᴺ : ℕ → ℕ → ℕ
∣ ᴢ - ᴢ ∣ᴺ = ᴢ
∣ ᴢ - ꜱ n ∣ᴺ = ꜱ n
∣ ꜱ m - ᴢ ∣ᴺ = ꜱ m
∣ ꜱ m - ꜱ n ∣ᴺ = ∣ m - n ∣ᴺ

∣_-_|ᴺ≤_ : ℕ → ℕ → Sens → Set
∣ n₁ - n₂ |ᴺ≤ s = ⟨ ∣ n₁ - n₂ ∣ᴺ ⟩ ≤ s

-- -- Theorem 1.2 (Sensitivity Type Soundness at Base Types).

sound : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e s s′ r₁ r₂ r′₁ r′₂ ℾ Σ₀ sb}
  → ℾ ⊢ ø → ℾ ⊢ ø → ⟨ ø , ø ⟩∈𝒢⟦ zero ː ℾ ⟧
  → Γ , Σ₀ ⊢ e ⦂ (sƛ⦂ ℝT ∥ sb ⇒[ zero ∔ [ s ] ] ℝT) , zero
  → ∣ r₁ - r₂ |ᴺ≤ s′
  → ø ⊢ e `app (`ℝ r₁) ⇓ 𝓇 r′₁
  → ø ⊢ e `app (`ℝ r₂) ⇓ 𝓇 r′₂
  → ∣ r′₁ - r′₂ |ᴺ≤ (s × s′)
sound {r′₁ = r′₁} {r′₂} ⊢ø₁ ⊢ø₂ r[⊢ø₁,⊢ø₂] ⊢e ε (⊢`app {γ = γ₁} {e′ = e′₁} δ₁ δ₂ δ₃) (⊢`app {γ = γ₂} {e′ = e′₂} δ₄ δ₅ δ₆)
  = fp ⊢ø₁ ⊢ø₂ ⊢e r[⊢ø₁,⊢ø₂] (sƛ⦂ e′₁ ∥ γ₁ ) (sƛ⦂ e′₂ ∥ γ₂ ) (typeSafety ⊢e δ₁) (typeSafety ⊢e δ₄) ⟨ δ₁ , δ₄ ⟩
